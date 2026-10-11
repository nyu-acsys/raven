open Base
open Smt.SmtSolver.SmtSession

let best_effort f = ignore (Result.try_with f)

let rec write_all fd text offset =
  if offset < String.length text then begin
    let written = Unix.write_substring fd text offset (String.length text - offset) in
    assert (written > 0);
    write_all fd text (offset + written)
  end

let with_session ?(response_timeout = Some 0.05) ?(spawn_child = false) f =
  let response_read, response_write = Unix.pipe ~cloexec:true () in
  let query_read, query_write = Unix.pipe ~cloexec:true () in
  let log_file = Stdlib.Filename.temp_file "raven-smt-lifecycle-" ".smt2" in
  let log_out = Stdio.Out_channel.create log_file in
  let pid =
    if spawn_child then
      Some
        (Unix.create_process Stdlib.Sys.executable_name
           [| Stdlib.Sys.executable_name; "--ignore-stdin" |]
           Unix.stdin Unix.stdout Unix.stderr)
    else None
  in
  let session =
    {
      stack_height = 0;
      solver_state =
        {
          out_descr = query_write;
          in_descr = response_read;
          pid;
          log_out_chan = Some log_out;
          response_timeout;
          pending_input = "";
          closed = false;
        };
    }
  in
  Stdlib.Fun.protect
    ~finally:(fun () ->
      stop_solver session;
      best_effort (fun () -> Unix.close response_write);
      best_effort (fun () -> Unix.close query_read);
      best_effort (fun () -> Stdlib.Sys.remove log_file))
    (fun () -> f session response_write)

let test_buffered_replies () =
  with_session (fun session response_write ->
      write_all response_write "sat\r\nunsat\n" 0;
      assert (
        Result.equal String.equal (fun _ _ -> false) (read_response session) (Ok "sat"));
      assert (
        Result.equal String.equal (fun _ _ -> false) (read_response session) (Ok "unsat")))

let test_fragmented_reply () =
  with_session (fun session response_write ->
      write_all response_write "sa" 0;
      assert (
        match read_response session with Error Response_timeout -> true | _ -> false);
      assert (String.equal session.solver_state.pending_input "sa");
      write_all response_write "t\n" 0;
      assert (
        Result.equal String.equal (fun _ _ -> false) (read_response session) (Ok "sat")))

let test_partial_eof () =
  with_session (fun session response_write ->
      write_all response_write "sa" 0;
      Unix.close response_write;
      assert (match read_response session with Error End_of_stream -> true | _ -> false))

let test_idempotent_stop () =
  with_session (fun session _ ->
      let copy = { session with stack_height = 1 } in
      let log_out = Option.value_exn session.solver_state.log_out_chan in
      stop_solver session;
      stop_solver copy;
      assert session.solver_state.closed;
      assert copy.solver_state.closed;
      assert (
        Result.is_error
          (Result.try_with (fun () -> Stdio.Out_channel.output_string log_out "closed")));
      assert (Result.is_error (Result.try_with (fun () -> write_text copy "closed"))))

let test_forced_stop_and_reap () =
  with_session ~spawn_child:true (fun session _ ->
      let pid = Option.value_exn session.solver_state.pid in
      let started = Unix.gettimeofday () in
      stop_solver session;
      assert (Float.(Unix.gettimeofday () -. started < 1.5));
      assert (
        match Result.try_with (fun () -> Unix.waitpid [ Unix.WNOHANG ] pid) with
        | Error (Unix.Unix_error (Unix.ECHILD, _, _)) -> true
        | _ -> false))

let test_original_error_survives_broken_pipe () =
  let pipe_read, pipe_write = Unix.pipe () in
  let response_read, response_write = Unix.pipe () in
  let result =
    Stdlib.Fun.protect
      ~finally:(fun () ->
        best_effort (fun () -> Unix.close pipe_read);
        best_effort (fun () -> Unix.close pipe_write);
        best_effort (fun () -> Unix.close response_write))
      (fun () ->
        Unix.close pipe_read;
        let session =
          {
            stack_height = 0;
            solver_state =
              {
                out_descr = pipe_write;
                in_descr = response_read;
                pid = None;
                log_out_chan = None;
                response_timeout = None;
                pending_input = "";
                closed = false;
              };
          }
        in
        Result.try_with (fun () ->
            Stdlib.Fun.protect
              ~finally:(fun () -> stop_solver session)
              (fun () -> failwith "original verification error")))
  in
  assert (
    match result with
    | Error (Failure message) -> String.equal message "original verification error"
    | _ -> false)

let rec ignore_stdin () =
  ignore (Unix.select [] [] [] 60.);
  ignore_stdin ()

let () =
  if
    Stdlib.Array.length Stdlib.Sys.argv > 1
    && String.equal Stdlib.Sys.argv.(1) "--ignore-stdin"
  then ignore_stdin ()
  else begin
    test_buffered_replies ();
    test_fragmented_reply ();
    test_partial_eof ();
    test_idempotent_stop ();
    test_forced_stop_and_reap ();
    test_original_error_survives_broken_pipe ()
  end
