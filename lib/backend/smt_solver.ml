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
    heapchunk_compare : smt_ident;
    field_fpu : smt_ident option;
    (* heapchunk_compare chunk1 chunk2 should return true if chunk1 <= chunk2 *)
  }

  type pred_trnsl = {
    pred_heap : term;
    pred_sort: sort;
    pred_args: sort list;
    pred_heap_sort: sort;
    pred_constr : smt_ident;
    pred_def : Callable.func_def;
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

  type data_constr = {
    constr : smt_ident
  }

  type data_destr = {
    destr : smt_ident
  }

  type smt_trnsl =
  | Field of field_trnsl
  | Type of sort
  | Var of var_trnsl
  | Pred of pred_trnsl
  | Func of func_trnsl
  | DataConstr of data_constr 
  | DataDestr of data_destr

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

  let find_term_exn env name = 
    match find env name with
    | Some (Field field_trnsl) -> field_trnsl.field_heap
    | Some (Var var_trnsl) -> var_trnsl.var_symbol
    | Some (Pred pred_trnsl) -> pred_trnsl.pred_heap
    | Some _ -> error_simple "find_term failed; found something in env which is not a term"
    | None -> error_simple "find_term failed; elem not found in env"

  let push_ident (tbl, stk) ident : t = (tbl, ident :: stk)
  let pop_ident (tbl, stk) : t = match stk with | _ :: tl -> (tbl, tl) | [] -> raise (Failure "Empty ident stack")

  let stack_name (_tbl, stk) : string = 
    List.fold stk ~init:"" ~f:(fun str ident -> (Ident.to_string ident) ^ "." ^ str)

  let mk_qual_ident (_tbl, stk) iden : qual_ident =
    QualIdent.make (List.rev stk) iden

  let mk_qual_ident_qi (_tbl, stk) qual_iden : qual_ident =
    QualIdent.(make (List.rev stk @ qual_iden.qual_path) qual_iden.qual_base)

  let flatten_env (tbl, _) : (smt_trnsl qual_ident_map) =
    (* Used to compress all the lists in the tbl into one list. This function is only used to find all heaps to reset them for while loops. In particular the output of this function should not be propagated forward. *)

    let rec compress_env_helper tbl mp : (smt_trnsl qual_ident_map) =
      match tbl with
      | [] -> mp
      | t :: ts -> 
        let mp = 
          List.fold (Map.to_alist t) ~init:mp ~f:(fun mp (quant_iden, smt_trnsl) ->
            match Map.find mp quant_iden with
            | None -> Map.add_exn mp ~key:quant_iden ~data:smt_trnsl
            | Some _ ->
              mp
          )
        in
        compress_env_helper ts mp

    in

    compress_env_helper tbl (Map.empty (module QualIdent))


  
  let trnsl_to_string (smt_trnsl: smt_trnsl) : string = 
    match smt_trnsl with
    | Field field_trnsl -> "Field: " ^ (Util.Print.string_of_format pr_term field_trnsl.field_heap) ^ " : " ^ (Util.Print.string_of_format pr_sort field_trnsl.field_sort)
    | Type sort -> "Type: " ^ (Util.Print.string_of_format pr_sort sort)
    | Var var_trnsl -> (Printf.sprintf "Var: %s; sort: %s" (Util.Print.string_of_format pr_term var_trnsl.var_symbol) (Util.Print.string_of_format pr_sort var_trnsl.var_sort))
    | Pred pred_trnsl -> "Pred: " ^ (Util.Print.string_of_format pr_term pred_trnsl.pred_heap)
    | Func func_trnsl -> "Func: " ^ (Util.Print.string_of_format pr_ident func_trnsl.func_symbol)
    | DataConstr data_constr -> "DataConstr: " ^ (Util.Print.string_of_format pr_ident data_constr.constr)
    | DataDestr data_destr -> "DataDestr: " ^ (Util.Print.string_of_format pr_ident data_destr.destr)

  let rec to_string (tbl, stk : t) =
    let rec list_to_string t =
      match t with
      | [] -> " "
      | (k, v) :: ms ->
          (QualIdent.to_string k ^ " -> " ^ trnsl_to_string v ^ "\n")
          ^ list_to_string ms
    in

    (match stk with
    | [] -> ""
    | _ -> stack_name (tbl, stk)
    ) ^

    (match tbl with
    | [] -> "end\n\n"
    | t :: ts ->
        " :: [ "
        ^ list_to_string (Map.to_alist t)
        ^ " ]\n" ^ to_string (ts, []))

  (* let trnsl_to_smt_ident (smt_trnsl: smt_trnsl) : smt_ident = *)


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
  | str -> raise (Generic_Error ("Unexpected solver output: " ^ str))


let is_unsat session = 
  Int.incr num_of_sat_queries;
  write session (mk_check_sat ());
  match (read session) with
  | "unsat" -> true
  | "sat" -> false
  | "unknown" -> false
  | str -> raise (Generic_Error ("Unexpected solver output: " ^ str))
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


let assert_not session expr =
  let session = push session in

  assert_expr session (mk_app Not [expr]);

  if is_unsat session then 
    let session = pop session in
    session
  else smt_error @@ (Printf.sprintf "Exhaling following expression failed:\n'%s'" (Util.Print.string_of_format pr_term expr))

(* --- *)

module PreambleConsts = struct
  let loc_ident = SMTIdent.make "$Loc"
  let loc_sort = FreeSort (loc_ident, [])

  let frac_heapchunk_sort_ident = SMTIdent.make "$FracHeapChunk"
  let frac_heap_null_ident = SMTIdent.make "$FracHeapNull"
  let frac_heap_null = mk_const (Ident frac_heap_null_ident)
  let frac_chunk_constr_ident = SMTIdent.make "$FracChunkConstr"
  let frac_heap_top_ident = SMTIdent.make "$FracHeapTop"
  let frac_heap_top = mk_const (Ident frac_heap_top_ident)
  let frac_val_destr_ident = SMTIdent.make "$FracVal"

  let frac_own_destr_ident = SMTIdent.make "$FracOwn"

  (* let heap_chunk_ident = SMTIdent.make "$HeapChunk"
  let heap_null_ident = SMTIdent.make "$HeapNull"
  let heap_chunk_constr_ident = SMTIdent.make "$ChunkConstr" *)


  let heap_sort_ident = SMTIdent.make "$OwnHeap"
  (* let heap_sort_ident = SMTIdent.make "$OwnHeap" *)

  let pred_heap_sort_ident = SMTIdent.make "$PredHeap"

  let int_frac_chunk_add_ident = SMTIdent.make "$IntFracChunkAdd"
  let int_frac_chunk_subtract_ident = SMTIdent.make "$IntFracChunkSubtract"
  let int_frac_heap_valid_ident = SMTIdent.make "$IntFracHeapValid"

  let int_heapchunk_compare_ident = SMTIdent.make "$IntHeapChunkCompare"

  let bool_frac_chunk_add_ident = SMTIdent.make "$BoolFracChunkAdd"
  let bool_frac_chunk_subtract_ident = SMTIdent.make "$BoolFracChunkSubtract"
  let bool_frac_heap_valid_ident = SMTIdent.make "$BoolFracHeapValid"
  let bool_heapchunk_compare_ident = SMTIdent.make "$BoolHeapChunkCompare"

  let loc_frac_chunk_add_ident = SMTIdent.make "$LocFracChunkAdd"
  let loc_frac_chunk_subtract_ident = SMTIdent.make "$LocFracChunkSubtract"
  let loc_frac_heap_valid_ident = SMTIdent.make "$LocFracHeapValid"
  let loc_heapchunk_compare_ident = SMTIdent.make "$LocHeapChunkCompare"

end

let mk_frac_heapchunk_sort field_sort : sort = FreeSort (PreambleConsts.frac_heapchunk_sort_ident, [field_sort])

let mk_own_heap_sort field_sort : sort = FreeSort (PreambleConsts.heap_sort_ident, [field_sort])

let mk_frac_own_heap_sort field_sort : sort = mk_own_heap_sort (mk_frac_heapchunk_sort field_sort)

let mk_pred_heap_sort pred_sort : sort = FreeSort (PreambleConsts.pred_heap_sort_ident , [pred_sort])

let frac_chunk_constr v_term r_term : term = mk_app (Ident PreambleConsts.frac_chunk_constr_ident) [v_term; r_term]

let declare_new_fieldheap (field_trnsl: SmtEnv.field_trnsl) (new_heap_name: smt_ident) (session: session) : unit =
  write session (mk_declare_const new_heap_name (mk_own_heap_sort field_trnsl.field_sort));
  write session (mk_assert (mk_app (Ident field_trnsl.field_heap_valid) [mk_const (Ident new_heap_name)]));
  ()

let declare_new_predheap (pred_trnsl: SmtEnv.pred_trnsl) (new_heap_name: smt_ident) (session: session) : unit =
  write session (mk_declare_const new_heap_name pred_trnsl.pred_heap_sort);

  let index_ident = SMTIdent.make "$index" in

  let index_term = mk_const (Ident index_ident) in



  write session (mk_assert (mk_forall [index_ident, pred_trnsl.pred_sort]
    (mk_geq (mk_select (mk_const (Ident new_heap_name)) index_term) (mk_const (IntConst 0)))
  ));
  ()



let add_frac_field_heap_functions field_sort field_heap_valid field_heap_add_chunk field_heap_subtract_chunk heapchunk_compare session : unit =
  let open PreambleConsts in
  let field_heap_sort = mk_frac_own_heap_sort field_sort in

  let heap_ident = SMTIdent.make "heap" in
  let l_ident = SMTIdent.make "l" in

  let heap_term = mk_app (Ident heap_ident) [] in
  let l_term = mk_app (Ident l_ident) [] in

  let i_term = term_of_string "i" in
  let r_term = term_of_string "r" in

  let annot_frac_heap_top = (mk_annot (frac_heap_top) (As (mk_frac_heapchunk_sort field_sort))) in

  write session 
  (mk_declare_fun field_heap_valid [field_heap_sort] BoolSort);

  write session
  (mk_assert (mk_binder Forall 
    [(heap_ident, field_heap_sort); 
    (l_ident, PreambleConsts.loc_sort)] 
    
    (mk_impl 
        (mk_app (Ident field_heap_valid) [heap_term])

        (mk_match (mk_select heap_term l_term)
          [(frac_heap_null, mk_const (BoolConst true));
          (frac_chunk_constr i_term r_term, mk_and [(mk_leq (mk_const (IntConst 0)) r_term); (mk_geq (mk_const (IntConst 1)) r_term)]);
          (frac_heap_top, mk_const (BoolConst false));
          ]
        )
    )
  ));

  let x1_arg = SMTIdent.make "x1" in
  let x2_arg = SMTIdent.make "x2" in

  let v1_term = term_of_string "v1" in
  let v2_term = term_of_string "v2" in
  let r1_term = term_of_string "r1" in
  let r2_term = term_of_string "r2" in

  write session
  (mk_define_fun field_heap_add_chunk [(x1_arg, mk_frac_heapchunk_sort field_sort); (x2_arg, mk_frac_heapchunk_sort field_sort)] (mk_frac_heapchunk_sort field_sort) 
  
    (mk_match (mk_const (Ident x1_arg))
      [
        (frac_heap_null, mk_const (Ident x2_arg));
        (frac_chunk_constr v1_term r1_term, 
          (mk_match (mk_const (Ident x2_arg))
            [
              (frac_heap_null, mk_const (Ident x1_arg));
              (
                frac_chunk_constr v2_term r2_term,
                (mk_ite 
                  (mk_eq v1_term v2_term) 
                  (frac_chunk_constr v1_term (mk_app Plus [r1_term; r2_term]))
                  annot_frac_heap_top
                )
              );
              (frac_heap_top, annot_frac_heap_top);
            ]
          )
        );
        (frac_heap_top, annot_frac_heap_top);
      ]
    )
  );

  write session
  (mk_define_fun field_heap_subtract_chunk [(x1_arg, mk_frac_heapchunk_sort field_sort); (x2_arg, mk_frac_heapchunk_sort field_sort)] (mk_frac_heapchunk_sort field_sort)

    (mk_match (mk_const (Ident x2_arg))
      [
        (frac_heap_null, mk_const (Ident x1_arg));
        (frac_chunk_constr v2_term r2_term, 
          (mk_match (mk_const (Ident x1_arg))
            [
              (frac_heap_null, (mk_annot (frac_heap_top) (As (mk_frac_heapchunk_sort field_sort))));
              (
                frac_chunk_constr v1_term r1_term,
                (mk_ite (mk_eq v1_term v2_term)
                  (mk_ite (mk_eq r1_term r2_term)
                    (mk_annot (frac_heap_null) (As (mk_frac_heapchunk_sort field_sort)))
                    (mk_ite (mk_gt r1_term r2_term)
                      (frac_chunk_constr v1_term (mk_app Minus [r1_term; r2_term]))
                      annot_frac_heap_top
                    )
                  )
                  annot_frac_heap_top
                )
              );
              (frac_heap_top, annot_frac_heap_top);
            ]
          )
        );
        (frac_heap_top, annot_frac_heap_top)
      ]
    )
  );

  write session
  (mk_define_fun heapchunk_compare [(x1_arg, mk_frac_heapchunk_sort field_sort); (x2_arg, mk_frac_heapchunk_sort field_sort)] BoolSort

    (mk_match (mk_const (Ident x1_arg))
      [
        (frac_heap_null, mk_const (BoolConst true));

        (frac_chunk_constr v1_term r1_term, 
          (mk_match (mk_const (Ident x2_arg))
            [
              (frac_heap_null, mk_const (BoolConst false));

              (
                frac_chunk_constr v2_term r2_term,
                (mk_ite (mk_eq v1_term v2_term)
                  (mk_leq r1_term r2_term)
                  (mk_const (BoolConst false))
                )
              );
              (frac_heap_top, (mk_const (BoolConst false)));
            ]
          )
        );
        (frac_heap_top, (mk_const (BoolConst false)))
      ]
    )
  );

  ()

let add_ra_field_heap_functions field_sort field_heap_valid field_valid heapchunk_compare field_heap_subtract_chunk session : unit = 
  let field_heap_sort = mk_own_heap_sort field_sort in

  let heap_ident = SMTIdent.make "heap" in
  let l_ident = SMTIdent.make "l" in

  let heap_term = mk_app (Ident heap_ident) [] in
  let l_term = mk_app (Ident l_ident) [] in

  write session
  (mk_define_fun field_heap_valid [(heap_ident, field_heap_sort)] BoolSort
    (mk_binder Forall [l_ident, PreambleConsts.loc_sort]
      (mk_app (Ident field_valid) [(mk_select heap_term l_term)])
    )
  );

  let x1_arg = SMTIdent.make "x1" in
  let x2_arg = SMTIdent.make "x2" in

  write session
  (mk_define_fun heapchunk_compare [(x1_arg, field_sort); (x2_arg, field_sort)] BoolSort
    (mk_app (Ident field_valid) [(mk_app (Ident field_heap_subtract_chunk) [mk_const (Ident x2_arg); mk_const (Ident x1_arg)])]
    )
  );
  ()


let init () : session =
  let session = start_solver () in
  let open PreambleConsts in

  let options_list = [
    SetOption  (":timeout", "2000", None);
  ] in

  let list_of_cmds = 
    let t_param_ident = SMTIdent.make "T" in
    let t_param_sort = FreeSort (t_param_ident, []) in
    
    [
    mk_declare_sort loc_ident 0;
    
    
    mk_declare_datatype (frac_heapchunk_sort_ident, [t_param_ident], [
      (frac_heap_null_ident, []); 
      (frac_chunk_constr_ident, [frac_val_destr_ident, t_param_sort; frac_own_destr_ident, RealSort]);
      (frac_heap_top_ident, []);
    ]);

    (* ownHeap *)

    mk_define_sort heap_sort_ident [t_param_ident] (ArraySort (loc_sort, t_param_sort));

    mk_define_sort pred_heap_sort_ident [t_param_ident] (ArraySort (t_param_sort, IntSort))

  ] in

  (* preamble *)
  List.iter options_list ~f:(write session);
  List.iter list_of_cmds ~f:(write session);

  
  add_frac_field_heap_functions IntSort int_frac_heap_valid_ident int_frac_chunk_add_ident int_frac_chunk_subtract_ident int_heapchunk_compare_ident session;
  add_frac_field_heap_functions BoolSort bool_frac_heap_valid_ident bool_frac_chunk_add_ident bool_frac_chunk_subtract_ident bool_heapchunk_compare_ident session;
  add_frac_field_heap_functions loc_sort loc_frac_heap_valid_ident loc_frac_chunk_add_ident loc_frac_chunk_subtract_ident loc_heapchunk_compare_ident session;

  write_comment session "End of Preamble";
  write_comment session "";
  write_comment session "";

  session
