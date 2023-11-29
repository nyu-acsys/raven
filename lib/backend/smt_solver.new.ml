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
    pred_def : Callable.call_def;
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

  let trnsl_to_string (smt_trnsl: smt_trnsl) : string = 
    match smt_trnsl with
    | Field field_trnsl -> "Field: " ^ (Util.Print.string_of_format pr_term field_trnsl.field_heap) ^ " : " ^ (Util.Print.string_of_format pr_sort field_trnsl.field_sort)
    | Type sort -> "Type: " ^ (Util.Print.string_of_format pr_sort sort)
    | Var var_trnsl -> (Printf.sprintf "Var: %s; sort: %s" (Util.Print.string_of_format pr_term var_trnsl.var_symbol) (Util.Print.string_of_format pr_sort var_trnsl.var_sort))
    | Pred pred_trnsl -> "Pred: " ^ (Util.Print.string_of_format pr_term pred_trnsl.pred_heap)
    | Func func_trnsl -> "Func: " ^ (Util.Print.string_of_format pr_ident func_trnsl.func_symbol)
    | DataConstr data_constr -> "DataConstr: " ^ (Util.Print.string_of_format pr_ident data_constr.constr)
    | DataDestr data_destr -> "DataDestr: " ^ (Util.Print.string_of_format pr_ident data_destr.destr)
end

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


  let check_valid session expr =
    let session = push session in
    assert_expr session (mk_app Not [expr]);

    if is_unsat session then 
      let session = pop session in
      session
    else smt_error @@ (Printf.sprintf "Exhaling following expression failed:\n'%s'" (Util.Print.string_of_format pr_term expr))
end


type smt_env = {
  smtTbl: SmtEnv.smt_trnsl qual_ident_map;
  session: SmtSession.session;
  path_conditions: term list;
}

type state = {
  tbl: SymbolTbl.t;
  smt_env: smt_env;
}

type 'a t = state -> (state * 'a)

let smt_env_to_string (smt_env: smt_env) : string =
  Printf.sprintf "smtTbl: { %s }\n\npath_conditions: %s" 
    (QualIdentMap.iter (fun key value -> Printf.sprintf "%d --> %d\n" key value) smt_env.smtTbl)

    (List.to_string ~f:(Util.Print.string_of_format pr_term)smt_env.path_conditions)

let to_string (state: state) : string =
  smt_env_to_string state.smt_env


let write state cmd =
  SmtSession.write state.smt_env.session cmd
  
let write_comment state cmnt =
  SmtSession.write_comment state.smt_env.session cmnt

let push (state: state) = 
  let session = SmtSession.push state.smt_env.session in
  { state with smt_env = { state.smt_env with session = session } }

let push_path_condn (term: term) (state: state) = 
  let path_conditions = term :: state.smt_env.path_conditions in
  { state with smt_env = { state.smt_env with path_conditions = path_conditions } }

let pop_path_condn (state: state) = 
  let path_conditions = List.tl_exn state.smt_env.path_conditions in
  { state with smt_env = { state.smt_env with path_conditions = path_conditions } }

let is_sat (state: state) : bool =
  SmtSession.is_sat state.smt_env.session

let is_unsat (state: state) : bool = 
  SmtSession.is_unsat state.smt_env.session

let assert_expr (state: state) (expr: term) : unit = 
  SmtSession.assert_expr state.smt_env.session (mk_impl (mk_and state.smt_env.path_conditions) expr)

let check_valid (state: state) (expr: term) : state = 
  let session = SmtSession.check_valid state.smt_env.session (mk_impl (mk_and state.smt_env.path_conditions) expr) in

  { state with smt_env = { state.smt_env with session = session } }


  let update_env (state: state) (new_vars: (qual_ident * smt_ident) list) : state = 
    let new_vars_map = List.fold new_vars ~init: (Map.empty (module QualIdent)) ~f:(fun map (quant_iden, smt_ident) ->
      match Map.find map quant_iden with
      | None -> Map.add_exn map ~key:quant_iden ~data:smt_ident
      | Some smt_ident' ->
        if smt_ident'.ident_num >= smt_ident.ident_num then
          map
        else
          Map.set map ~key:quant_iden ~data:smt_ident
    ) in
  
    let smtEnv = state.smt_env in
  
    let smtEnv = List.fold (Map.to_alist new_vars_map) ~init:smtEnv ~f:(fun env (qual_iden, smt_iden) ->
      match Map.find env.smtTbl qual_iden with
      | None -> error_simple @@ Printf.sprintf "update_env called with new variable '%s'; not found in present env. smtEnv: %s" (QualIdent.to_string qual_iden) (smt_env_to_string smtEnv)
      | Some (Field field_trnsl) -> 
        let new_field_trnsl = { field_trnsl with
          field_heap = mk_const (Ident smt_iden);
        } in
        (* Previous binding is overwritten by Map.set *)
        let smtTbl = QualIdentMap.set env qual_iden (Field new_field_trnsl) in
        { env with smtTbl = smtTbl }
  
      | Some (Var var_trnsl) ->
        let new_var_trnsl = { var_trnsl with
          var_symbol = mk_const (Ident smt_iden);
        } in
        let smtTbl = QualIdentMap.set env qual_iden (Var new_var_trnsl) in
        { env with smtTbl = smtTbl }
  
      | Some (Pred pred_trnsl) ->
        let new_pred_trnsl = { pred_trnsl with
          pred_heap = mk_const (Ident smt_iden);
        } in
        let smtTbl = QualIdentMap.set env qual_iden (Pred new_pred_trnsl) in
        { env with smtTbl = smtTbl }
  
      | _ -> error_simple "update_env called with func/type; not expected to update these."
    ) in
  
    { state with smt_env = smtEnv }



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

let declare_new_fieldheap (field_trnsl: SmtEnv.field_trnsl) (new_heap_name: smt_ident) (session: SmtSession.session) : unit =
  let open SmtSession in
  write session (mk_declare_const new_heap_name (mk_own_heap_sort field_trnsl.field_sort));
  write session (mk_assert (mk_app (Ident field_trnsl.field_heap_valid) [mk_const (Ident new_heap_name)]));
  ()

let declare_new_predheap (pred_trnsl: SmtEnv.pred_trnsl) (new_heap_name: smt_ident) (state: state) : unit =
  let open SmtSession in
  write state.smt_env.session (mk_declare_const new_heap_name pred_trnsl.pred_heap_sort);

  let index_ident = SMTIdent.make "$index" in

  let index_term = mk_const (Ident index_ident) in

  write state.smt_env.session (mk_assert (mk_forall [index_ident, pred_trnsl.pred_sort]
    (mk_geq (mk_select (mk_const (Ident new_heap_name)) index_term) (mk_const (IntConst 0)))
  ));
  ()



let add_frac_field_heap_functions field_sort field_heap_valid field_heap_add_chunk field_heap_subtract_chunk heapchunk_compare state : unit =
  let open PreambleConsts in
  let open SmtSession in
  let field_heap_sort = mk_frac_own_heap_sort field_sort in

  let heap_ident = SMTIdent.make "heap" in
  let l_ident = SMTIdent.make "l" in

  let heap_term = mk_app (Ident heap_ident) [] in
  let l_term = mk_app (Ident l_ident) [] in

  let i_term = term_of_string "i" in
  let r_term = term_of_string "r" in

  let annot_frac_heap_top = (mk_annot (frac_heap_top) (As (mk_frac_heapchunk_sort field_sort))) in

  write state.smt_env.session 
  (mk_declare_fun field_heap_valid [field_heap_sort] BoolSort);

  write state.smt_env.session
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

  write state.smt_env.session
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

  write state.smt_env.session
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

  write state.smt_env.session
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

let add_ra_field_heap_functions field_sort field_heap_valid field_valid heapchunk_compare field_heap_subtract_chunk (state: state) : unit = 
  let open SmtSession in
  let field_heap_sort = mk_own_heap_sort field_sort in

  let heap_ident = SMTIdent.make "heap" in
  let l_ident = SMTIdent.make "l" in

  let heap_term = mk_app (Ident heap_ident) [] in
  let l_term = mk_app (Ident l_ident) [] in

  write state.smt_env.session
  (mk_define_fun field_heap_valid [(heap_ident, field_heap_sort)] BoolSort
    (mk_binder Forall [l_ident, PreambleConsts.loc_sort]
      (mk_app (Ident field_valid) [(mk_select heap_term l_term)])
    )
  );

  let x1_arg = SMTIdent.make "x1" in
  let x2_arg = SMTIdent.make "x2" in

  write state.smt_env.session
  (mk_define_fun heapchunk_compare [(x1_arg, field_sort); (x2_arg, field_sort)] BoolSort
    (mk_app (Ident field_valid) [(mk_app (Ident field_heap_subtract_chunk) [mk_const (Ident x2_arg); mk_const (Ident x1_arg)])]
    )
  );
  ()


let init tbl : state =
  let open SmtSession in
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

  let smtEnv = {
    smtTbl = Map.empty (module QualIdent); 
    session = session;
    path_conditions = [];
  } in

  let state = {
    tbl = tbl;
    smt_env = smtEnv;
  } in

  (* preamble *)
  List.iter options_list ~f:(write session);
  List.iter list_of_cmds ~f:(write session);

  
  add_frac_field_heap_functions IntSort int_frac_heap_valid_ident int_frac_chunk_add_ident int_frac_chunk_subtract_ident int_heapchunk_compare_ident state;
  add_frac_field_heap_functions BoolSort bool_frac_heap_valid_ident bool_frac_chunk_add_ident bool_frac_chunk_subtract_ident bool_heapchunk_compare_ident state;
  add_frac_field_heap_functions loc_sort loc_frac_heap_valid_ident loc_frac_chunk_add_ident loc_frac_chunk_subtract_ident loc_heapchunk_compare_ident state;

  write_comment session "End of Preamble";
  write_comment session "";
  write_comment session "";

  state




(* --- *)

module Syntax = struct
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

let lft_smtEnv (f: smt_env -> smt_env) : state -> state = fun s -> { s with smt_env = f s.smt_env }
