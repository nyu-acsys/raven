open Base
open Unix
open Util__Error
open SmtLibAST
open Ast
(* open Rewriter *)


module SmtSession = struct
  let num_of_sat_queries = ref 0

  type solver_state = 
    { out_chan: Stdio.Out_channel.t;
      in_chan: Stdio.In_channel.t;
      (* pid: int; *)
      mutable response_count: int;
    }

  type session = { 
    log_file_name: string;
    log_out_chan: Stdio.Out_channel.t;
    mutable assert_count: int;
    mutable response_count: int;
    (* mutable sat_checked: (solver_state option * response) option; *)
    stack_height: int;
    (* signature: (arity list SymbolMap.t) option; *)
    (* user_sorts: sort IdMap.t; *)
    (* named_clauses: (string, form) Hashtbl.t option; *)
    solver_state: solver_state
  }

  let start_solver () = 
    (*let in_read, in_write = Unix.pipe () in
    let out_read, out_write = Unix.pipe () in
    let pid = Unix.create_process "z3" [| "smt2"; "-in" |] out_read in_write in_write in

    close out_read;
    close in_write;*)

    let in_chan, out_chan = Unix.open_process_args "z3" [| "smt2"; "-in" |] in
    
    let solver_state = {
      (*in_chan = in_channel_of_descr in_read;
      out_chan = out_channel_of_descr out_write;
        pid = pid;*)
      in_chan = in_chan;
      out_chan = out_chan;
      response_count = 0;
    } in

    let log_file_name = "log.smt" in

    {
      log_file_name = log_file_name;
      log_out_chan = Stdio.Out_channel.create log_file_name;
      assert_count = 0;
      response_count = 0;
      stack_height = 0;
      solver_state = solver_state;
    }

  let write session cmd =
    SmtLibAST.print_command session.log_out_chan cmd;
    SmtLibAST.print_command session.solver_state.out_chan cmd

  let stop_solver session = 
    write session @@ mk_exit ();
    Stdio.Out_channel.flush session.solver_state.out_chan;
    (* clean up resources *)
    (*Stdio.Out_channel.close_no_err session.solver_state.out_chan;
    Stdio.In_channel.close session.solver_state.in_chan;
    (try Unix.kill state.pid Sys.sigkill with Unix.Unix_error _ -> ())
      if solver.solver_state.pid <> 0 then ignore (Unix.waitpid [] state.pid))*)
    ignore @@ Unix.close_process (session.solver_state.in_chan, session.solver_state.out_chan)


  (* let read_from_chan session chan =
    let lexbuf = Lexing.from_channel chan in
    SmtLibLexer.set_file_name lexbuf session.log_file_name; 
    try
      SmtLibParser.output SmtLibLexer.token lexbuf
    with ProgError.Prog_error (pos, _) ->
      let tok = Lexing.lexeme lexbuf in
      let tail = SmtLibLexer.ruleTail "" lexbuf in
      let msg = 
        "failed to parse SMT solver response while parsing: " ^ tok ^ tail
      in
      ProgError.syntax_error pos (Some msg) *)

  let write_comment session cmnt =
    SmtLibAST.print_comment session.log_out_chan cmnt;
    SmtLibAST.print_comment session.solver_state.out_chan cmnt

  let read session = 
    let in_descr = 
      descr_of_in_channel session.solver_state.in_chan
        
    in

    Stdio.Out_channel.flush session.solver_state.out_chan;
    (* let rec loop () = *)
      let ready, _, _ = Unix.select [in_descr] [] [] (-1.) in

      let in_descr = Base.List.hd ready in
      match in_descr with
      | Some in_descr -> (
      let in_chan = in_channel_of_descr in_descr in
      let result = In_channel.input_line in_chan in
      match result with
      | None -> raise (Generic_Error "Read from SMT Solver returned nothing")
      | Some str -> str
      )
      | None -> raise (Generic_Error "Read from SMT Solver returned nothing")
      (* state.response_count <- state.response_count + 1; *)
      (* if state.response_count > session.response_count
      then begin
        session.response_count <- session.response_count + 1;
        Some state, result
      end *)
      (* else () *)
    (* in
    loop ()
    *)

  let is_sat session = 
    Int.incr num_of_sat_queries;
    write session (mk_check_sat ());
    match (read session) with
    | "sat" -> true
    | "unsat" -> false
    | "unknown" -> false
    | str -> raise (Generic_Error ("Unexpected solver output: " ^ str))


  let is_unsat session = 
    Int.incr num_of_sat_queries;
    write session (mk_check_sat ());
    match (read session) with
    | "unsat" -> true
    | "sat" -> false
    | "unknown" -> false
    | str -> raise (Generic_Error ("Unexpected solver output: " ^ str))

  let push session = 
    write session (mk_push 1);
    let new_session = { session with stack_height = session.stack_height + 1 } in
    new_session

  let pop session = 
    if session.stack_height <= 0 then error_simple "pop on empty stack" else
    write session (mk_pop 1);
    let new_session = { session with stack_height = session.stack_height - 1 } in
    new_session

  let assert_expr session expr =
    write session (mk_assert expr)


  let check_valid session expr =
    let session = push session in
    assert_expr session (Ast.Expr.mk_not expr);

    let res = is_unsat session in
    let session = pop session in
    res, session
    (* if is_unsat session then 
      let session = pop session in
      true, session
    else smt_error (Ast.Expr.to_loc expr) @@ (Printf.sprintf "Exhaling following expression failed:\n'%s'" (Util.Print.string_of_format Ast.Expr.pr expr)) *)
end


type smt_env = {
  (* smtTbl: SmtEnv.smt_trnsl qual_ident_map; *)
  session: SmtSession.session;
  path_conditions: term list;
}

(* type state = {
  tbl: SymbolTbl.t;
  smt_env: smt_env;
} *)

type 'a t = ('a, smt_env) Rewriter.t_ext

(* let smt_env_to_string (smt_env: smt_env) : string =
  Printf.sprintf "path_conditions: %a" 
    (* (QualIdentMap.iter (fun key value -> Printf.sprintf "%d --> %d\n" key value) smt_env.smtTbl) *)
    (Util.Print.pr_list_comma Expr.pr) smt_env.path_conditions

let to_string (state: state) : string =
  smt_env_to_string state.smt_env *)

let write cmd : unit t =
  let open Rewriter.Syntax in
  match cmd with
  | Assert _ -> Util.Error.internal_error (Util.Loc.dummy) "Cannot write assert command directly; use assume_expr instead"
  | _ ->
    let* smt_env = Rewriter.current_user_state in
    let _ = SmtSession.write smt_env.session cmd in

    Rewriter.return ()



  (* SmtSession.write state.smt_env.session cmd *)
  
let write_comment cmnt =
  let open Rewriter.Syntax in
  let* smt_env = Rewriter.current_user_state in
  let _ = SmtSession.write_comment smt_env.session cmnt in

  Rewriter.return ()

let push = 
  let open Rewriter.Syntax in
  let* smt_env = Rewriter.current_user_state in

  let session = SmtSession.push smt_env.session in
  let* _ = Rewriter.set_user_state { smt_env with session = session } in

  Rewriter.return ()

let pop = 
  let open Rewriter.Syntax in
  let* smt_env = Rewriter.current_user_state in

  let session = SmtSession.pop smt_env.session in
  let* _ = Rewriter.set_user_state { smt_env with session = session } in

  Rewriter.return ()

let push_path_condn (term: term) = 
  let open Rewriter.Syntax in
  let* smt_env = Rewriter.current_user_state in

  let path_conditions = term :: smt_env.path_conditions in
  let* _ = Rewriter.set_user_state { smt_env with path_conditions = path_conditions } in

  Rewriter.return ()

let pop_path_condn = 
  let open Rewriter.Syntax in
  let* smt_env = Rewriter.current_user_state in

  let path_conditions = Base.List.tl_exn smt_env.path_conditions in
  let* _ = Rewriter.set_user_state { smt_env with path_conditions = path_conditions } in

  Rewriter.return ()

let is_sat : bool t =
  let open Rewriter.Syntax in
  let* smt_env = Rewriter.current_user_state in

  Rewriter.return @@ SmtSession.is_sat smt_env.session

let is_unsat : bool t = 
  let open Rewriter.Syntax in
  let* smt_env = Rewriter.current_user_state in

  Rewriter.return @@ SmtSession.is_unsat smt_env.session

let assume_expr (expr: term) : unit t = 
  (* Externally facing command to assume expressions. Takes path_condns into account *)
  let open Rewriter.Syntax in
  let* smt_env = Rewriter.current_user_state in

  let expr = match smt_env.path_conditions with
    | [] -> expr
    | _ -> Ast.Expr.mk_impl (Ast.Expr.mk_and smt_env.path_conditions) expr 
  in

  let cmd = mk_assert expr in
  let _ = SmtSession.write smt_env.session cmd in

  Rewriter.return ()

let check_valid (expr: term) : bool t = 
  let open Rewriter.Syntax in
  let* smt_env = Rewriter.current_user_state in
  Logs.debug (fun m -> m "Checking validity of %a" Ast.Expr.pr_verbose expr);

  let res, session = SmtSession.check_valid smt_env.session (Ast.Expr.mk_impl (Ast.Expr.mk_and smt_env.path_conditions) expr) in

  let* _ = Rewriter.set_user_state  { smt_env with session = session } in

  Rewriter.return res


(* --- *)


let declare_tuple_sort (arity:int) : command =
  let tuple_sort_name = QualIdent.from_ident (Ident.make Util.Loc.dummy ("$tuple_" ^ (Int.to_string arity)) 0) in

  let params =
    Base.List.init arity ~f:(fun i -> QualIdent.from_ident (Ident.make Util.Loc.dummy ("X" ^ (Int.to_string i)) 0))
  in

  let constr = tuple_sort_name in
  let destrs = Base.List.init arity ~f:(fun i -> QualIdent.from_ident (Ident.make Util.Loc.dummy ("$tuple_" ^ (Int.to_string arity) ^ "_" ^ (Int.to_string i)) 0)) in

  let destrs_sorts = Base.List.map2_exn destrs params ~f:(fun destr param -> (destr, Ast.Type.mk_var Util.Loc.dummy param)) in

  mk_declare_datatype (tuple_sort_name, params, [ (constr, destrs_sorts) ])


let init () : smt_env =
  let open SmtSession in
  let session = start_solver () in
  let open PreambleConsts in

  let options_list = [
    SetOption  (":timeout", "2000", None);
  ] in

  let list_of_cmds = [
    mk_declare_sort loc_ident 0;
  ] in

  let list_of_cmds = list_of_cmds @ (Base.List.init 10 ~f:(fun i -> declare_tuple_sort (i+1))) in

  let smt_env = {
    session = session;
    path_conditions = [];
  } in

  (* preamble *)
  Base.List.iter options_list ~f:(write session);
  Base.List.iter list_of_cmds ~f:(write session);

  write_comment session "End of Preamble";
  write_comment session "";
  write_comment session "";

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
