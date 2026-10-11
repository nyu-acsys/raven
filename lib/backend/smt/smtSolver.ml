open Base
open Util
open SmtLibAst

type validity_result = Valid | Invalid | Inconclusive

let parse_sat_result = function
  | "sat" -> Ok Sat
  | "unsat" -> Ok Unsat
  | "unknown" -> Ok Unknown
  | str -> Error str

module SmtSession = struct
  type solver_state = {
    out_descr : Unix.file_descr;
    in_descr : Unix.file_descr;
    pid : int option;
    log_out_chan : Stdio.Out_channel.t option;
    response_timeout : float option;
    mutable pending_input : string;
    mutable closed : bool;
  }

  type session = { mutable stack_height : int; solver_state : solver_state }
  type read_error = Response_timeout | End_of_stream | Session_closed | Io_error of exn

  let create_session ?pid ?log_out_chan ~response_timeout ~input ~output () =
    {
      stack_height = 0;
      solver_state =
        {
          out_descr = output;
          in_descr = input;
          pid;
          log_out_chan;
          response_timeout;
          pending_input = "";
          closed = false;
        };
    }

  let best_effort f = ignore (Result.try_with f)

  let rec wait_for_exit pid deadline =
    match Result.try_with (fun () -> Unix.waitpid [ Unix.WNOHANG ] pid) with
    | Ok (waited, _) when waited <> 0 -> true
    | Error (Unix.Unix_error (Unix.ECHILD, _, _)) -> true
    | _ ->
        if Float.(Unix.gettimeofday () >= deadline) then false
        else begin
          best_effort (fun () -> ignore (Unix.select [] [] [] 0.01));
          wait_for_exit pid deadline
        end

  let reap_solver pid =
    if not (wait_for_exit pid (Unix.gettimeofday () +. 0.2)) then begin
      best_effort (fun () -> Unix.kill pid Stdlib.Sys.sigkill);
      if not (wait_for_exit pid (Unix.gettimeofday () +. 1.)) then
        Logs.warn (fun m -> m "Could not reap the Z3 process during session cleanup")
    end

  let stop_solver session =
    let state = session.solver_state in
    if not state.closed then begin
      state.closed <- true;
      (* Closing stdin requests exit without risking another write to a broken pipe. *)
      best_effort (fun () -> Unix.close state.out_descr);
      best_effort (fun () -> Unix.close state.in_descr);
      Option.iter state.log_out_chan ~f:Stdio.Out_channel.close_no_err;
      Option.iter state.pid ~f:(fun pid -> best_effort (fun () -> reap_solver pid))
    end

  let start_solver ?(logging = true) ?(response_timeout = Some 30.) () =
    (* Broken solver pipes must raise write errors instead of terminating Raven. *)
    best_effort (fun () ->
        Stdlib.Sys.set_signal Stdlib.Sys.sigpipe Stdlib.Sys.Signal_ignore);
    let log_out_chan =
      if logging then Some (Stdio.Out_channel.create "log.smt2") else None
    in
    let transferred = ref false in
    Stdlib.Fun.protect ~finally:(fun () ->
        if not !transferred then
          Option.iter log_out_chan ~f:Stdio.Out_channel.close_no_err)
    @@ fun () ->
    let stdin_read, stdin_write = Unix.pipe ~cloexec:true () in
    let close_descr fd = best_effort (fun () -> Unix.close fd) in
    Stdlib.Fun.protect ~finally:(fun () ->
        close_descr stdin_read;
        if not !transferred then close_descr stdin_write)
    @@ fun () ->
    let stdout_read, stdout_write = Unix.pipe ~cloexec:true () in
    let pid = ref None in
    Stdlib.Fun.protect ~finally:(fun () ->
        close_descr stdout_write;
        if not !transferred then begin
          close_descr stdout_read;
          Option.iter !pid ~f:(fun pid -> best_effort (fun () -> reap_solver pid))
        end)
    @@ fun () ->
    let child =
      Unix.create_process "z3" [| "z3"; "-in" |] stdin_read stdout_write Unix.stderr
    in
    pid := Some child;
    let session =
      create_session ~pid:child ?log_out_chan ~response_timeout ~input:stdout_read
        ~output:stdin_write ()
    in
    transferred := true;
    session

  let write_text session text =
    let state = session.solver_state in
    if state.closed then
      Error.internal_error Loc.dummy "Cannot write to a closed SMT session";
    let fail_write exn =
      Error.internal_error Loc.dummy
        ("Failed to write SMT session output: " ^ Exn.to_string exn)
    in
    Option.iter state.log_out_chan ~f:(fun out_chan ->
        match
          Result.try_with (fun () ->
              Stdio.Out_channel.output_string out_chan text;
              Stdio.Out_channel.flush out_chan)
        with
        | Ok () -> ()
        | Error exn -> fail_write exn);
    let rec output offset =
      if offset < String.length text then
        match
          Result.try_with (fun () ->
              Unix.write_substring state.out_descr text offset
                (String.length text - offset))
        with
        | Ok 0 -> Error.internal_error Loc.dummy "The Z3 input pipe accepted no data"
        | Ok count -> output (offset + count)
        | Error (Unix.Unix_error (Unix.EINTR, _, _)) -> output offset
        | Error exn -> fail_write exn
    in
    output 0

  let write_command session cmd = write_text session (SmtLibAst.command_to_string cmd)

  let write session cmd =
    match cmd with
    | Push _ | Pop _ | CheckSat _ | GetModel _ | GetUnsatCore _ | Exit _ ->
        Error.internal_error Loc.dummy
          "Cannot write a solver control command directly; use session operations"
    | _ -> write_command session cmd

  let write_comment session cmnt = write_text session (SmtLibAst.comment_to_string cmnt)

  let read_response session =
    let state = session.solver_state in
    let deadline =
      Option.map state.response_timeout ~f:(fun timeout ->
          Unix.gettimeofday () +. timeout)
    in
    let bytes = Bytes.create 4096 in
    let rec read_line () =
      if state.closed then Error Session_closed
      else
        match String.lfindi state.pending_input ~f:(fun _ c -> Char.equal c '\n') with
        | Some index ->
            let line = String.prefix state.pending_input index in
            state.pending_input <- String.drop_prefix state.pending_input (index + 1);
            Ok (String.chop_suffix_if_exists line ~suffix:"\r")
        | None -> (
            let remaining =
              Option.value_map deadline ~default:(-1.) ~f:(fun deadline ->
                  Float.max 0. (deadline -. Unix.gettimeofday ()))
            in
            if Float.(remaining = 0.) then Error Response_timeout
            else
              match
                Result.try_with (fun () -> Unix.select [ state.in_descr ] [] [] remaining)
              with
              | Error (Unix.Unix_error (Unix.EINTR, _, _)) -> read_line ()
              | Error exn -> Error (Io_error exn)
              | Ok ([], _, _) -> Error Response_timeout
              | Ok _ -> (
                  match
                    Result.try_with (fun () ->
                        Unix.read state.in_descr bytes 0 (Bytes.length bytes))
                  with
                  | Error
                      (Unix.Unix_error
                         ((Unix.EINTR | Unix.EAGAIN | Unix.EWOULDBLOCK), _, _)) ->
                      read_line ()
                  | Error exn -> Error (Io_error exn)
                  | Ok 0 -> Error End_of_stream
                  | Ok count ->
                      state.pending_input <-
                        state.pending_input ^ Stdlib.Bytes.sub_string bytes 0 count;
                      read_line ()))
    in
    read_line ()

  let read session =
    match read_response session with
    | Ok line -> line
    | Error End_of_stream ->
        Error.internal_error Loc.dummy
          "Lost communication with the Z3 process while checking this proof obligation \
           -- Z3 may have crashed or been killed; re-run with --verbosity=debug to \
           inspect log.smt2"
    | Error Response_timeout ->
        Error.internal_error Loc.dummy
          "Timed out waiting for a response from Z3 (re-run with --verbosity=debug to \
           inspect log.smt2)"
    | Error Session_closed ->
        Error.internal_error Loc.dummy "Cannot read from a closed SMT session"
    | Error (Io_error exn) ->
        Error.internal_error Loc.dummy ("Failed to read Z3 output: " ^ Exn.to_string exn)

  let check_sat session : sat_result =
    write_command session (mk_check_sat ());
    match parse_sat_result (read session) with
    | Ok result -> result
    | Error str ->
        Error.fail ~lbl:Internal Loc.dummy
          (Printf.sprintf
             "Z3 returned unexpected output while checking this proof obligation: %s \
              (re-run with --verbosity=debug to inspect log.smt2)"
             str)

  let push session =
    write_command session (mk_push 1);
    session.stack_height <- session.stack_height + 1

  let pop session =
    if session.stack_height <= 0 then Error.internal_error Loc.dummy "pop on empty stack";
    write_command session (mk_pop 1);
    session.stack_height <- session.stack_height - 1

  let with_scope session ~f =
    push session;
    let completed = ref false in
    Stdlib.Fun.protect
      ~finally:(fun () ->
        if not session.solver_state.closed then
          match Result.try_with (fun () -> pop session) with
          | Ok () -> ()
          | Error exn ->
              let backtrace = Stdlib.Printexc.get_raw_backtrace () in
              stop_solver session;
              if !completed then Stdlib.Printexc.raise_with_backtrace exn backtrace)
      (fun () ->
        let result = f () in
        completed := true;
        result)

  let assert_expr ?name session expr = write session (mk_assert ?name expr)

  let check_valid ?name session expr =
    with_scope session ~f:(fun () ->
        assert_expr ?name session (Ast.Expr.mk_not expr);
        match check_sat session with
        | Unsat -> Valid
        | Sat -> Invalid
        | Unknown -> Inconclusive)

  module ForTesting = struct
    type nonrec read_error = read_error =
      | Response_timeout
      | End_of_stream
      | Session_closed
      | Io_error of exn

    let of_owned_descriptors = create_session
    let read_response = read_response
    let stack_height session = session.stack_height
  end
end

type session = SmtSession.session

let init ?(logging = true) timeout : session =
  let response_timeout =
    if timeout > 0 then Some (Float.of_int timeout /. 1000.) else None
  in
  SmtSession.start_solver ~logging ~response_timeout ()

(** Closes and reaps the session without replacing an error from verification. *)
let stop (session : session) = SmtSession.stop_solver session
