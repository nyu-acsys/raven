open Base

(*open Util__Error*)
open Util
open SmtLibAst
open Ast
(* open Rewriter *)

type validity_result = Valid | Invalid | Inconclusive

let parse_sat_result = function
  | "sat" -> Ok Sat
  | "unsat" -> Ok Unsat
  | "unknown" -> Ok Unknown
  | str -> Error str

module SmtSession = struct
  let num_of_sat_queries = ref 0

  type solver_state = {
    out_descr : Unix.file_descr;
    in_descr : Unix.file_descr;
    pid : int option;
    log_out_chan : Stdio.Out_channel.t option;
    response_timeout : float option;
    mutable pending_input : string;
    mutable closed : bool;
  }

  type session = { stack_height : int; solver_state : solver_state }
  type read_error = Response_timeout | End_of_stream | Session_closed | Io_error of exn

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
      {
        stack_height = 0;
        solver_state =
          {
            out_descr = stdin_write;
            in_descr = stdout_read;
            pid = Some child;
            log_out_chan;
            response_timeout;
            pending_input = "";
            closed = false;
          };
      }
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

  let write session cmd = write_text session (SmtLibAst.command_to_string cmd)
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
    Int.incr num_of_sat_queries;
    write session (mk_check_sat ());
    match parse_sat_result (read session) with
    | Ok result -> result
    | Error str ->
        Error.fail ~lbl:Internal Loc.dummy
          (Printf.sprintf
             "Z3 returned unexpected output while checking this proof obligation: %s \
              (re-run with --verbosity=debug to inspect log.smt2)"
             str)

  let push session =
    write session (mk_push 1);
    let new_session = { session with stack_height = session.stack_height + 1 } in
    new_session

  let pop session =
    if session.stack_height <= 0 then Error.internal_error Loc.dummy "pop on empty stack"
    else write session (mk_pop 1);
    let new_session = { session with stack_height = session.stack_height - 1 } in
    new_session

  let assert_expr ?name session expr = write session (mk_assert ?name expr)

  let check_valid ?name session expr =
    let session = push session in
    assert_expr ?name session (Ast.Expr.mk_not expr);

    let result =
      match check_sat session with
      | Unsat -> Valid
      | Sat -> Invalid
      | Unknown -> Inconclusive
    in
    let session = pop session in
    (result, session)
end

type smt_env = {
  session : SmtSession.session;
  path_conditions : term list;
  auto_dependencies : Ast.CallGraph.Graph.t;
}

type 'a t = smt_env -> smt_env * 'a

(* let smt_env_to_string (smt_env: smt_env) : string =
     Printf.sprintf "path_conditions: %a"
       (* (QualIdentMap.iter (fun key value -> Printf.sprintf "%d --> %d\n" key value) smt_env.smtTbl) *)
       (Util.Print.pr_list_comma Expr.pr) smt_env.path_conditions

   let to_string (state: state) : string =
     smt_env_to_string state.smt_env *)

let write cmd : unit t =
  let open State.Syntax in
  match cmd with
  | Assert _ ->
      Util.Error.internal_error Util.Loc.dummy
        "Cannot write assert command directly; use assume_expr instead"
  | _ ->
      let+ smt_env = get_state in
      SmtSession.write smt_env.session cmd

(* SmtSession.write state.smt_env.session cmd *)

let write_comment cmnt : unit t =
  let open State.Syntax in
  let+ smt_env = get_state in
  SmtSession.write_comment smt_env.session cmnt

let push =
  let open State.Syntax in
  map_state ~f:(fun smt_env -> { smt_env with session = SmtSession.push smt_env.session })

let pop =
  let open State.Syntax in
  map_state ~f:(fun smt_env -> { smt_env with session = SmtSession.pop smt_env.session })

let push_path_condn (term : term) =
  let open State.Syntax in
  map_state ~f:(fun smt_env ->
      let path_conditions = term :: smt_env.path_conditions in
      { smt_env with path_conditions })

let pop_path_condn =
  let open State.Syntax in
  map_state ~f:(fun smt_env ->
      let path_conditions = Base.List.tl_exn smt_env.path_conditions in
      { smt_env with path_conditions })

let check_sat : sat_result t =
  let open State.Syntax in
  let+ smt_env = get_state in
  SmtSession.check_sat smt_env.session

let assume_expr ?name (expr : term) : unit t =
  (* Externally facing command to assume expressions. Takes path_condns into account *)
  let open State.Syntax in
  let+ smt_env = get_state in

  let expr =
    match smt_env.path_conditions with
    | [] -> expr
    | _ -> Ast.Expr.mk_impl (Ast.Expr.mk_and smt_env.path_conditions) expr
  in

  let cmd = mk_assert ?name (Ast.Expr.drop_trivially_true expr) in
  SmtSession.write smt_env.session cmd

let check_valid ?name (expr : term) : validity_result t =
  let open State.Syntax in
  let* smt_env = get_state in
  Logs.debug (fun m -> m "Checking validity of %a" Ast.Expr.pr_verbose expr);

  let expr =
    match smt_env.path_conditions with
    | [] -> expr
    | _ -> Ast.Expr.mk_impl (Ast.Expr.mk_and smt_env.path_conditions) expr
  in

  let res, session = SmtSession.check_valid ?name smt_env.session expr in

  let+ _ = set_state { smt_env with session } in

  res

(* --- *)

let declare_tuple_sort (arity : int) : command =
  let tuple_sort_name =
    QualIdent.from_ident (Ident.make Util.Loc.dummy ("$tuple_" ^ Int.to_string arity) 0)
  in

  let params =
    Base.List.init arity ~f:(fun i ->
        QualIdent.from_ident (Ident.make Util.Loc.dummy ("X" ^ Int.to_string i) 0))
  in

  let constr = tuple_sort_name in
  let destrs =
    Base.List.init arity ~f:(fun i ->
        QualIdent.from_ident
          (Ident.make Util.Loc.dummy
             ("$tuple_" ^ Int.to_string arity ^ "_" ^ Int.to_string i)
             0))
  in

  let destrs_sorts =
    Base.List.map2_exn destrs params ~f:(fun destr param ->
        (destr, Ast.Type.mk_var param))
  in

  mk_declare_datatype (tuple_sort_name, params, [ (constr, destrs_sorts) ])

let init ?(logging = true) diagnostics timeout : smt_env =
  let open SmtSession in
  let response_timeout =
    if timeout > 0 then Some (Float.of_int timeout /. 1000.) else None
  in
  let session = start_solver ~logging ~response_timeout () in
  let initialized = ref false in
  Stdlib.Fun.protect ~finally:(fun () -> if not !initialized then stop_solver session)
  @@ fun () ->
  let open PreambleConsts in
  let options_list =
    [
      SetOption (":timeout", Int.to_string timeout, None);
      (*SetOption (":produce-unsat-cores", "true", None);*)
      SetOption (":auto-config", "false", None);
      SetOption (":smt.mbqi", "false", None);
      SetOption (":smt.case_split", "3", None);
      SetOption (":smt.candidate_models", "true", None);
      (* Call nlsat on the non-linear part of a query only after many final checks:
         most proofs do not need it, and early calls make the search slower and its
         time more variable. *)
      SetOption (":smt.arith.nl.delay", "200", None);
      (*SetOption (":smt.macro_finder", "true", None);*)
    ]
    @ if diagnostics then [ SetOption (":smt.qi.profile", "true", None) ] else []
  in

  let list_of_cmds =
    [
      mk_declare_sort loc_ident 0;
      mk_declare_const
        (QualIdent.from_ident (Ident.make Util.Loc.dummy "null" 0))
        Type.ref;
      mk_declare_sort atomic_token_ident 0;
    ]
  in

  let smt_env =
    { session; path_conditions = []; auto_dependencies = Ast.CallGraph.Graph.empty }
  in

  (* preamble *)
  Base.List.iter options_list ~f:(write session);
  Base.List.iter list_of_cmds ~f:(write session);

  write_comment session "End of Preamble";
  write_comment session "";
  write_comment session "";

  initialized := true;
  smt_env

(** Closes and reaps the session without replacing an error from verification. *)
let stop (smt_env : smt_env) = SmtSession.stop_solver smt_env.session

(** Declares exactly the generic tuple sorts ([$tuple_n]) the program being checked
    actually needs, rather than an arbitrary fixed range. [arities] is computed from the
    fully elaborated program (see [TupleArities]) once parsing and front-end processing
    have completed, which is why this is a separate step from [init]: at the point [init]
    runs (before any parsing), the input isn't known yet. *)
let declare_tuple_sorts (smt_env : smt_env) (arities : int list) : smt_env =
  let open SmtSession in
  (match arities with
  | [] -> ()
  | _ ->
      write_comment smt_env.session "Tuple sorts used by this program";
      Base.List.iter arities ~f:(fun arity ->
          write smt_env.session (declare_tuple_sort arity));
      write_comment smt_env.session "");

  smt_env

(* --- *)

(* module Syntax = struct
     let return a = fun s -> (s, a)

     module Let_syntax = struct
       let bind m ~f = fun sin ->
         let sout, res = m sin in
         f res sout

       let return = return

       let map m ~f = fun sin ->
         let sout, res = m sin in
         (sout, f res)

       let both m1 m2 = fun sin ->
         let s1, res1 = m1 sin in
         let s2, res2 = m2 s1 in
         (s2, (res1, res2))
     end

     open Let_syntax

     let (let+) (m: state -> state * 'a) (f: 'a -> 'b) : (state -> state * 'b) = map m ~f
     let (and+) = both
     let (let* ) (m: state -> state * 'a) (f: 'a -> state -> state * 'b) : (state -> state * 'b) = bind m ~f
     let (and* ) = both
   end

   let lft_smtEnv (f: smt_env -> smt_env) : state -> state = fun s -> { s with smt_env = f s.smt_env } *)
