open Base
open Unix
open Util__Error
open SmtLibAST
open Ast

module SmtEnv = struct
  type field_trnsl = {
    field_heap : term;
    field_sort : sort;
    field_heap_valid: smt_ident;
    field_heap_add_chunk: smt_ident;
    field_heap_subtract_chunk: smt_ident;
  }

  type pred_trnsl = {
    pred_heap : term;
    pred_sort: sort;
    pred_heap_sort: sort;
    pred_constr : smt_ident;
  }

  type var_trnsl = {
    var_symbol : term;
    var_sort : sort;
  }

  type func_trnsl = {
    func_symbol : smt_ident;
    func_args : sort list;
    func_return : sort;
  }

  type smt_trnsl =
  | Field of field_trnsl
  | Type of sort
  | Var of var_trnsl
  | Pred of pred_trnsl
  | Func of func_trnsl

  type t = (smt_trnsl qual_ident_map) list * (Ident.t list)

  let push (tbl, stk) : t = (Map.empty (module QualIdent) :: tbl), stk

  let pop (tbl, stk) =
    match tbl with [] -> raise (Failure "Empty symbol table") | _ :: ts -> (ts, stk)

  let add (tbl,stk : t) name elem : t =
    match tbl with
    | [] -> raise (Failure "Empty symbol table")
    | map :: ts -> 
      match Map.find map name with
      | None -> (Map.add_exn map ~key:name ~data:elem) :: ts, stk
      | Some _ ->
        print_debug ("Overriding " ^ (QualIdent.to_string name));
        (Map.set map ~key:name ~data:elem) :: ts, stk

  let find_local tbl name =
    match tbl with [] -> None | map :: _ -> Map.find name map

  let rec find (tbl, stk : t) name =
    match tbl with
    | [] -> None
    | map :: ts -> (
        match Map.find map name with None -> find (ts, stk) name | Some id -> Some id
      )

  let push_ident (tbl, stk) ident : t = (tbl, ident :: stk)
  let pop_ident (tbl, stk) : t = match stk with | _ :: tl -> (tbl, tl) | [] -> raise (Failure "Empty ident stack")

  let stack_name (_tbl, stk) : string = 
    List.fold stk ~init:"." ~f:(fun str ident -> (Ident.to_string ident) ^ str)
  
  let mk_qual_ident (_tbl, stk) iden : qual_ident =
    QualIdent.make stk iden
end

type smt_env = SmtEnv.t

let num_of_sat_queries = ref 0

type solver_state = 
    { out_chan: Stdio.Out_channel.t;
      in_chan: Stdio.In_channel.t;
      pid: int;
      mutable response_count: int;
    }

type session = { 
  log_file_name: string;
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
  let in_read, in_write = Unix.pipe () in
  let out_read, out_write = Unix.pipe () in
  let pid = Unix.create_process "z3" [| "smt2"; "-in" |] out_read in_write in_write in

  close out_read;
  close in_write;

  let solver_state = {
    in_chan = in_channel_of_descr in_read;
    out_chan = out_channel_of_descr out_write;
    pid = pid;
    response_count = 0;
  } in

  {
    log_file_name = "log.smt";
    assert_count = 0;
    response_count = 0;
    stack_height = 0;
    solver_state = solver_state;
  }

let write session cmd =
  SmtLibAST.print_command session.solver_state.out_chan cmd

(* let writeln session cmd = 
  write session (cmd ^ "\n") *)

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


let read session = 
  let in_descr = 
    descr_of_in_channel session.solver_state.in_chan
       
  in

  Stdio.Out_channel.flush session.solver_state.out_chan;
  (* let rec loop () = *)
    let ready, _, _ = Unix.select [in_descr] [] [] (-1.) in

    let in_descr = List.hd ready in
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
  | _ -> raise (Generic_Error "Unexpected solver output")


let is_unsat session = 
  Int.incr num_of_sat_queries;
  write session (mk_check_sat ());
  match (read session) with
  | "unsat" -> true
  | "sat" -> false
  | "unknown" -> false
  | _ -> raise (Generic_Error "Unexpected solver output")
(* in
  session.sat_checked <- Some response;
  match snd response with
  | Sat -> Some true
  | Unsat -> Some false
  | Unknown -> None
  | Error e -> fail session e
  | _ -> fail session "unexpected response from prover" *)
  
(* let add_preamble () =
  let ic = open_in "./preamble.smt2" in
  try
    let line = Stdio.In_channel.input_line ic in
    (* read line, discard \n *)
    Stdio.print_endline line;
    (* write the result to stdout *)
    (* flush stdout; *)
    (* write on the underlying device now *)
    close_in ic
    (* close the input channel *)
  with e ->
    (* some unexpected exception occurs *)
    close_in_noerr ic;
    (* emergency closing *)
    raise e

  () *)

let pop session = 
  if session.stack_height <= 0 then error_simple "pop on empty stack" else
  write session (mk_pop 1);
  let new_session = { session with stack_height = session.stack_height - 1 } in
  new_session

let push session = 
  write session (mk_pop 1);
  let new_session = { session with stack_height = session.stack_height + 1 } in
  new_session

let init () : session =
  let session = start_solver () in

  (* let _ = add_preamble () in *)

  session
  (* writeln session "(declare-const x Int)";
  writeln session "(assert (= x 5))";
  is_sat session; *)


let assert_expr session expr =
  write session (mk_assert expr)


let assert_not session expr =
  let session = push session in

  assert_expr session (mk_app Not [expr]);

  if is_unsat session then 
    let session = pop session in
    session
  else smt_error "UNSAT"

(* --- *)

let fracOwnHeapSort = SMTIdent.make "FracOwnHeap"

let fracHeapChunk = SMTIdent.make "FracHeapChunk"

let mk_frac_heapchunk_sort field_sort : sort = FreeSort (fracHeapChunk, [field_sort])

let mk_frac_own_heap_sort field_sort : sort = FreeSort (fracOwnHeapSort, [field_sort])
