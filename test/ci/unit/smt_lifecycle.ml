open Base
open Raven
open Backend
open Smt.SmtSolver
open SmtSession
open ForTesting

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
    of_owned_descriptors ?pid ~log_out_chan:log_out ~response_timeout ~input:response_read
      ~output:query_write ()
  in
  Stdlib.Fun.protect
    ~finally:(fun () ->
      stop session;
      best_effort (fun () -> Unix.close response_write);
      best_effort (fun () -> Unix.close query_read);
      best_effort (fun () -> Stdlib.Sys.remove log_file))
    (fun () -> f session response_write log_out pid)

let test_buffered_replies () =
  with_session (fun session response_write _ _ ->
      write_all response_write "sat\r\nunsat\n" 0;
      assert (
        Result.equal String.equal (fun _ _ -> false) (read_response session) (Ok "sat"));
      assert (
        Result.equal String.equal (fun _ _ -> false) (read_response session) (Ok "unsat")))

let test_fragmented_reply () =
  with_session (fun session response_write _ _ ->
      write_all response_write "sa" 0;
      assert (
        match read_response session with Error Response_timeout -> true | _ -> false);
      write_all response_write "t\n" 0;
      assert (
        Result.equal String.equal (fun _ _ -> false) (read_response session) (Ok "sat")))

(* A solver that does not respond in time makes the query time out and closes the
   session. *)
let test_unresponsive_solver () =
  with_session (fun session _ _ _ ->
      assert (
        match check_valid session (Ast.Expr.mk_bool true) with
        | Timeout -> true
        | _ -> false);
      assert (match read_response session with Error Session_closed -> true | _ -> false))

let test_partial_eof () =
  with_session (fun session response_write _ _ ->
      write_all response_write "sa" 0;
      Unix.close response_write;
      assert (match read_response session with Error End_of_stream -> true | _ -> false))

let test_idempotent_stop () =
  with_session (fun session _ log_out _ ->
      let copy = session in
      stop session;
      stop copy;
      assert (match read_response copy with Error Session_closed -> true | _ -> false);
      assert (
        Result.is_error
          (Result.try_with (fun () -> Stdio.Out_channel.output_string log_out "closed")));
      assert (Result.is_error (Result.try_with (fun () -> write_comment copy "closed"))))

let test_forced_stop_and_reap () =
  with_session ~spawn_child:true (fun session _ _ pid ->
      let pid = Option.value_exn pid in
      let started = Unix.gettimeofday () in
      stop session;
      assert (Float.(Unix.gettimeofday () -. started < 1.5));
      assert (
        match Result.try_with (fun () -> Unix.waitpid [ Unix.WNOHANG ] pid) with
        | Error (Unix.Unix_error (Unix.ECHILD, _, _)) -> true
        | Error (Unix.Unix_error (Unix.EBADF, _, _)) when Stdlib.Sys.win32 -> true
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
          of_owned_descriptors ~response_timeout:None ~input:response_read
            ~output:pipe_write ()
        in
        Result.try_with (fun () ->
            Stdlib.Fun.protect
              ~finally:(fun () -> stop session)
              (fun () -> failwith "original verification error")))
  in
  assert (
    match result with
    | Error (Failure message) -> String.equal message "original verification error"
    | _ -> false)

let test_scope_cleanup_failure ~body_fails =
  best_effort (fun () ->
      Stdlib.Sys.set_signal Stdlib.Sys.sigpipe Stdlib.Sys.Signal_ignore);
  let pipe_read, pipe_write = Unix.pipe () in
  let response_read, response_write = Unix.pipe () in
  let session =
    of_owned_descriptors ~response_timeout:None ~input:response_read ~output:pipe_write ()
  in
  Stdlib.Fun.protect
    ~finally:(fun () ->
      stop session;
      best_effort (fun () -> Unix.close pipe_read);
      Unix.close response_write)
    (fun () ->
      let result =
        Result.try_with (fun () ->
            with_scope session ~f:(fun () ->
                Unix.close pipe_read;
                if body_fails then failwith "original scope error"))
      in
      assert (
        match result with
        | Error (Failure message) when body_fails ->
            String.equal message "original scope error"
        | Error _ when not body_fails -> true
        | _ -> false);
      assert (match read_response session with Error Session_closed -> true | _ -> false))

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
    test_unresponsive_solver ();
    test_partial_eof ();
    test_idempotent_stop ();
    test_forced_stop_and_reap ();
    test_original_error_survives_broken_pipe ();
    test_scope_cleanup_failure ~body_fails:true;
    test_scope_cleanup_failure ~body_fails:false
  end
