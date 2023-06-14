open Smt_solver
open Ast
open Base
open Frontend
open SmtLibAST

let add_type (tp: Module.type_alias) ?(alias_name: QualIdent.t option) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: Smt_solver.session) : (smt_env * Smt_solver.session)  =
  let fully_qual_ident_fn ident =
    match alias_name with
    | None -> SmtEnv.mk_qual_ident smtEnv ident
    | Some qual_iden -> (SmtEnv.mk_qual_ident_qi smtEnv (QualIdent.append qual_iden ident))

  in


  let fully_qualified_ident = fully_qual_ident_fn tp.type_alias_name

  in

  let smt_ident = SMTIdent.make (QualIdent.to_string fully_qualified_ident) in

  match tp.type_alias_def with
  | None -> (
    let tp_trns = FreeSort (smt_ident, []);
    in

    let _ = Smt_solver.write session (mk_declare_sort smt_ident 0) in
    let smtEnv = SmtEnv.add smtEnv fully_qualified_ident (Type tp_trns) in

    smtEnv, session
  )

  | Some (App (Data variant_decl_list, [], _)) -> 
    let smtEnv, constrs_list = List.fold_map variant_decl_list ~init:smtEnv 
    ~f:(fun smtEnv variant_decl ->
      let constr_fully_qual_ident = fully_qual_ident_fn variant_decl.variant_name in
      let constr_smt_ident = SMTIdent.make (QualIdent.to_string constr_fully_qual_ident) in

      let smtEnv, destr_list = List.fold_map variant_decl.variant_args ~init:smtEnv
      ~f:(fun smtEnv var_decl ->
        let destr_fully_qual_ident = fully_qual_ident_fn var_decl.var_name in
        let destr_smt_ident = SMTIdent.make (QualIdent.to_string destr_fully_qual_ident) in

        let destr_type = var_decl.var_type in
        let destr_smt_sort = Callable_checker.lookup_type destr_type tbl smtEnv in

        let smtEnv = SmtEnv.add smtEnv destr_fully_qual_ident (DataDestr {destr = destr_smt_ident;}) in

        smtEnv, (destr_smt_ident, destr_smt_sort)
      ) in


      let smtEnv = SmtEnv.add smtEnv constr_fully_qual_ident (DataConstr {constr = constr_smt_ident;}) in

      smtEnv, (constr_smt_ident, destr_list)

    ) in

    Smt_solver.write session (mk_declare_datatype (smt_ident, [], constrs_list));

    let tp_trnsl = FreeSort (smt_ident, []) in
    let smtEnv = SmtEnv.add smtEnv fully_qualified_ident (Type tp_trnsl) in

    smtEnv, session
    
  | Some tp_expr ->
    let tp_trns = Callable_checker.lookup_type tp_expr tbl smtEnv in

    (* Smt_solver.write session (mk_declare_datatype) *)

    let smtEnv = SmtEnv.add smtEnv fully_qualified_ident (Type tp_trns) in
    smtEnv, session

let add_field (field: Module.field_def) ?(alias_name: QualIdent.t option) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: Smt_solver.session) : (smt_env * Smt_solver.session) =
  let name_qual_ident =
    match alias_name with
    | None -> SmtEnv.mk_qual_ident smtEnv field.field_name
    | Some qual_iden -> (SmtEnv.mk_qual_ident_qi smtEnv (QualIdent.append qual_iden field.field_name))

  in

  let fully_qualified_name = (QualIdent.to_string name_qual_ident) in

  let field_heap_ident = SMTIdent.fresh (fully_qualified_name ^"@OwnHeap") in

  let field_heap_term = mk_const (Ident field_heap_ident) in

    let create_new_frac_field_trnsl tp_expr : SmtEnv.field_trnsl * term = 
      (let field_sort = Callable_checker.lookup_type tp_expr tbl smtEnv in
      let field_heap_valid = SMTIdent.make (fully_qualified_name ^ "@HeapValid") in
      let field_heap_add_chunk = SMTIdent.make (fully_qualified_name ^ "@HeapAddChunk") in
      let field_heap_subtract_chunk = SMTIdent.make (fully_qualified_name ^ "@HeapSubtractChunk") in
      let heapchunk_compare = SMTIdent.make (fully_qualified_name ^ "@HeapChunkCompare") in

      let _ = add_frac_field_heap_functions field_sort field_heap_valid field_heap_add_chunk field_heap_subtract_chunk heapchunk_compare session in
      {
        field_heap = field_heap_term;
        field_sort = mk_frac_heapchunk_sort field_sort;
        field_heap_valid = field_heap_valid;
        field_heap_add_chunk = field_heap_add_chunk;
        field_heap_subtract_chunk = field_heap_subtract_chunk;
        heapchunk_compare = heapchunk_compare;
        field_fpu = None;
      }, (mk_annot (PreambleConsts.frac_heap_null) (As (mk_frac_heapchunk_sort field_sort))) 
      ) 
    
  in


  let (field_trnsl, ident_heapchunk_term: SmtEnv.field_trnsl * term) = (match field.field_type with

  | App (Int, _, _) ->
    let field_sort = Callable_checker.lookup_type field.field_type tbl smtEnv in
    {
      field_heap = field_heap_term;
      field_sort = mk_frac_heapchunk_sort field_sort;
      field_heap_valid = PreambleConsts.int_frac_heap_valid_ident;
      field_heap_add_chunk = PreambleConsts.int_frac_chunk_add_ident;
      field_heap_subtract_chunk = PreambleConsts.int_frac_chunk_subtract_ident;
      heapchunk_compare = PreambleConsts.int_heapchunk_compare_ident;
      field_fpu = None;
    }, (mk_annot (PreambleConsts.frac_heap_null) (As (mk_frac_heapchunk_sort field_sort)))

  | App (Bool, _, _) ->
    let field_sort = Callable_checker.lookup_type field.field_type tbl smtEnv in
    {
      field_heap = field_heap_term;
      field_sort = mk_frac_heapchunk_sort field_sort;
      field_heap_valid = PreambleConsts.bool_frac_heap_valid_ident;
      field_heap_add_chunk = PreambleConsts.bool_frac_chunk_add_ident;
      field_heap_subtract_chunk = PreambleConsts.bool_frac_chunk_subtract_ident;
      heapchunk_compare = PreambleConsts.bool_heapchunk_compare_ident;
      field_fpu = None;
    }, (mk_annot (PreambleConsts.frac_heap_null) (As (mk_frac_heapchunk_sort field_sort)))

  | App (Ref, _, _) ->
    let field_sort = Callable_checker.lookup_type field.field_type tbl smtEnv in
    {
      field_heap = field_heap_term;
      field_sort = mk_frac_heapchunk_sort field_sort;
      field_heap_valid = PreambleConsts.loc_frac_heap_valid_ident;
      field_heap_add_chunk = PreambleConsts.loc_frac_chunk_add_ident;
      field_heap_subtract_chunk = PreambleConsts.loc_frac_chunk_subtract_ident;
      heapchunk_compare = PreambleConsts.loc_heapchunk_compare_ident;
      field_fpu = None;
    }, (mk_annot (PreambleConsts.frac_heap_null) (As (mk_frac_heapchunk_sort field_sort)))
  
  | App (Var qual_ident, _, _) -> (
    match SymbolTbl.find tbl qual_ident with
    | Some (RAModDecl (ra_mod, _)) -> (
      let (field_type: Type.t) = (match ra_mod.module_decl.mod_decl_rep with
      | None -> Util.Error.error field.field_loc "RA Module does not have a rep type."
      | Some ident ->
        let rep_type_fully_qual_ident = QualIdent.append qual_ident ident in
        (App (Var rep_type_fully_qual_ident, [], Type.dummy_attr))
      ) in
      let field_sort = Callable_checker.lookup_type field_type tbl smtEnv in
      let field_heap_valid = SMTIdent.make (fully_qualified_name ^ "@HeapValid") in
      let field_heap_add_chunk = (match SmtEnv.find smtEnv (QualIdent.append qual_ident (Ident.make "comp" 0)) with
      | Some (Func func_trnsl) -> func_trnsl.func_symbol
      | _ -> Util.Error.error field.field_loc "'comp' function not found in RA"
      ) in
      let field_fpu = (match SmtEnv.find smtEnv (QualIdent.append qual_ident (Ident.make "fpuAllowed" 0)) with
      | Some (Func func_trnsl) -> func_trnsl.func_symbol
      | _ -> Util.Error.error field.field_loc "'fpuApply' function not found in RA"
      ) in
      let field_heap_subtract_chunk = (match SmtEnv.find smtEnv (QualIdent.append qual_ident (Ident.make "frame" 0)) with
      | Some (Func func_trnsl) -> func_trnsl.func_symbol
      | _ -> Util.Error.error field.field_loc "'frame' function not found in RA"
      ) in
      let field_valid = (match SmtEnv.find smtEnv (QualIdent.append qual_ident (Ident.make "valid" 0)) with
      | Some (Func func_trnsl) -> func_trnsl.func_symbol
      | _ -> Util.Error.error field.field_loc "'valid' function not found in RA"
      ) in
      let heapchunk_compare = SMTIdent.make (fully_qualified_name ^ "@HeapChunkCompare") in

      let _ = add_ra_field_heap_functions field_sort field_heap_valid field_valid heapchunk_compare field_heap_subtract_chunk session in
      (* add_ra_field_heap_functions only adds field_heap_valid and heap_chunk_compare *)

      let ident_qual_ident = QualIdent.append qual_ident (Ident.make "id" 0) in
      let ident_heapchunk_term = Callable_checker.translate_expr (App (Var ident_qual_ident, [], Expr.mk_attr Util.Loc.dummy field_type)) tbl smtEnv in

    {
      field_heap = field_heap_term;
      field_sort = field_sort;
      field_heap_valid = field_heap_valid;
      field_heap_add_chunk = field_heap_add_chunk;
      field_heap_subtract_chunk = field_heap_subtract_chunk;
      heapchunk_compare = heapchunk_compare;
      field_fpu = Some field_fpu;
    }, ident_heapchunk_term
    )
    | _ -> 
      create_new_frac_field_trnsl field.field_type

  )
  | _ -> 
    create_new_frac_field_trnsl field.field_type

  
  )

  in

  declare_new_fieldheap field_trnsl field_heap_ident session;


  let loc_ident = SMTIdent.make "loc" in
  let loc_term = mk_const (Ident loc_ident) in
  
  let cmd = (mk_assert (mk_binder Forall [(loc_ident, PreambleConsts.loc_sort)]
    (mk_eq 
      ident_heapchunk_term
      (mk_select field_heap_term loc_term)
    )
  )) in

  Smt_solver.write session cmd;

  let smtEnv = SmtEnv.add smtEnv (SmtEnv.mk_qual_ident smtEnv field.field_name) (Field field_trnsl) in
  
  smtEnv, session


let add_var_def (var_def: Stmt.var_def) ?(alias_name: QualIdent.t option) (tbl: SymbolTbl.t) (smtEnv: SmtEnv.t) (session: Smt_solver.session) : (SmtEnv.t * Smt_solver.session) = 
  let fully_qualified_name =
    match alias_name with
    | None -> SmtEnv.mk_qual_ident smtEnv var_def.var_decl.var_name
    | Some qual_iden -> (SmtEnv.mk_qual_ident_qi smtEnv (QualIdent.append qual_iden var_def.var_decl.var_name))

  in

  let fresh_var_name = SMTIdent.fresh (QualIdent.to_string fully_qualified_name) in
  let fresh_var_term = mk_const (Ident fresh_var_name) in
  let var_sort = Callable_checker.lookup_type var_def.var_decl.var_type tbl smtEnv in

  Smt_solver.write session (mk_declare_const fresh_var_name var_sort);

  let smtEnv = SmtEnv.add smtEnv fully_qualified_name (Var {var_symbol = fresh_var_term; var_sort = var_sort}) in

  match var_def.var_init with 
  | None -> smtEnv, session
  | Some expr -> 
    let expr_trnsl = Callable_checker.translate_expr expr tbl smtEnv in

    Smt_solver.write session (mk_assert (mk_eq fresh_var_term expr_trnsl));

    smtEnv, session


let rec add_mod_alias (m: Module.t) (alias_name: QualIdent.t) (tbl: SymbolTbl.t) (smtEnv: SmtEnv.t) (session: Smt_solver.session) : (SmtEnv.t * Smt_solver.session) = 
  (* TODO: handle formal args to partially-instantiated modules *)

  let smtEnv, session = Map.fold m.module_decl.mod_decl_mod_aliases ~init:(smtEnv, session) ~f:(fun ~key:_mod_name ~data:mod_alias (smtEnv, session) ->
    let fully_qualified_mod_alias_name = SmtEnv.mk_qual_ident_qi smtEnv (QualIdent.append alias_name mod_alias.mod_alias_name) in

    let m = (match SymbolTbl.find tbl fully_qualified_mod_alias_name with
    | Some (ModDecl (m, _)) | Some (RAModDecl (m, _)) -> m
    | _ -> Util.Error.error m.module_decl.mod_decl_loc "Unexpected element found in SymbolTbl. Expected ModDecl."
    ) in
    
    add_mod_alias m (QualIdent.append alias_name m.module_decl.mod_decl_name) tbl smtEnv session
  ) in

  let smtEnv, session = Map.fold m.module_decl.mod_decl_mod_defs ~init:(smtEnv, session) ~f:(fun ~key:mod_name ~data:_mod_decl' (smtEnv, session) -> 
    let fully_qual_mod_name = SmtEnv.mk_qual_ident_qi smtEnv (QualIdent.append alias_name mod_name) in

    let m = (match SymbolTbl.find tbl fully_qual_mod_name with
    | Some (ModDecl (m, _)) -> m
    | _ -> Util.Error.error m.module_decl.mod_decl_loc "Unexpected element found in SymbolTbl. Expected ModDecl."
    ) in

    add_mod_alias m (QualIdent.append alias_name m.module_decl.mod_decl_name) tbl smtEnv session
  ) in
  
  let smtEnv, session = Map.fold m.module_decl.mod_decl_types ~init:(smtEnv, session) ~f:(fun ~key:_tp_name ~data:tp_alias (smtEnv, session) -> 
    add_type tp_alias ~alias_name:(alias_name) tbl smtEnv session) in

  let smtEnv, session = Map.fold m.module_decl.mod_decl_fields ~init:(smtEnv, session) ~f:(fun ~key:_field_name ~data:field_def (smtEnv, session) -> add_field field_def ~alias_name:alias_name tbl smtEnv session) in

  let smtEnv, session = List.fold m.members.vars ~init:(smtEnv, session) ~f:(fun (smtEnv, session) var_def -> 
    add_var_def var_def ~alias_name tbl smtEnv session
  ) in

  let smtEnv, session = List.fold m.members.call_defs ~init:(smtEnv, session) ~f:(fun (smtEnv, session) call_decl ->
    add_mod_alias_callable call_decl alias_name tbl smtEnv session
    
  ) in

  (* TODO: Also add variables. Probably need to change the definition of module_decl in AST to store var_def instead of var_decl. *)

  smtEnv, session

and add_mod_alias_callable (callable: Callable.t) (alias_name: QualIdent.t) (tbl: SymbolTbl.t) (smtEnv: SmtEnv.t) (session: Smt_solver.session) : (SmtEnv.t * Smt_solver.session) =
  let call_decl = (Callable.to_decl callable) in
  match call_decl.call_decl_kind with
  | Proc -> 
    smtEnv, session
  | Lemma ->
    (match callable with 
      | FuncDef _ -> Util.Error.error call_decl.call_decl_loc "Pred/Invariant cannot be ProcDef. Error"
      | ProcDef proc_def ->
        (match call_decl.call_decl_formals, call_decl.call_decl_precond, proc_def.proc_body with
        | [], [], None -> 
          (* Treating lemmas from interfaces with no arguments and no preconditions as axioms. *)
          
          Smt_solver.write_comment session ("Asserting axiom " ^ (Ident.to_string call_decl.call_decl_name));
          List.fold call_decl.call_decl_postcond ~init:(smtEnv, session) ~f:(fun (smtEnv, session) post_cond ->
            Callable_checker.check_basic_stmt (Spec (Inhale, post_cond)) [] tbl smtEnv session (call_decl.call_decl_loc)
          )
        | _ ->
          smtEnv, session))
  | Func ->
    Callable_checker.check_module_callable callable ~alias_name:alias_name tbl smtEnv session
  | Pred 
  | Invariant ->
    match callable with
    | FuncDef func_def ->
      Callable_checker.initialize_pred func_def ~alias_name:alias_name tbl smtEnv session
    | ProcDef _proc_def ->
      Util.Error.error call_decl.call_decl_loc "Pred/Invariant cannot be ProcDef. Error"


let rec check_module (m: Module.t) (tbl: SymbolTbl.t) (smtEnv: SmtEnv.t) (session: Smt_solver.session) : (SmtEnv.t * Smt_solver.session) =
  let smtEnv = SmtEnv.push_ident smtEnv m.module_decl.mod_decl_name in

  Smt_solver.write_comment session "";
  Smt_solver.write_comment session "";
  Smt_solver.write_comment session ("Entering module " ^ SmtEnv.stack_name smtEnv);

  let formal_args_mod_aliases = List.map m.module_decl.mod_decl_formals ~f:(
    fun mod_name -> 
      Map.find_exn m.module_decl.mod_decl_mod_aliases mod_name
  ) in

  let mod_aliases = formal_args_mod_aliases @ m.members.mod_aliases in
  (* TODO: The order in which module aliases are added needs to be more carefully chosen; there may be dependencies between them that need to be respected. *)

  let (smtEnv, session) = List.fold mod_aliases ~init:(smtEnv, session) ~f:(fun (smtEnv, session) mod_alias ->
    let fully_qualified_mod_alias_name = SmtEnv.mk_qual_ident smtEnv mod_alias.mod_alias_name in

    let mod1 = (match SymbolTbl.find tbl fully_qualified_mod_alias_name with
    | Some (ModDecl (m, _)) | Some (RAModDecl (m, _))-> m
    | _ -> Util.Error.error m.module_decl.mod_decl_loc "Unexpected element found in SymbolTbl. Expected ModDecl."
    ) in
    
    Smt_solver.write_comment session @@ Printf.sprintf "Adding mod_alias %s for module %s" (Ident.to_string mod_alias.mod_alias_name) (Ident.to_string m.module_decl.mod_decl_name);
    add_mod_alias mod1 (QualIdent.from_ident mod_alias.mod_alias_name) tbl smtEnv session
  ) in
  
  let (smtEnv,session) = List.fold m.members.mod_defs ~init:(smtEnv,session) ~f:(fun (smtEnv,session) m -> 
    check_module m tbl smtEnv session
  ) in

  let (smtEnv,session) = List.fold m.members.types ~init:(smtEnv,session) ~f:(fun (smtEnv,session) tp -> add_type tp tbl smtEnv session) in

  let (smtEnv,session) = List.fold m.members.fields ~init:(smtEnv,session) ~f:(fun (smtEnv,session) field -> add_field field tbl smtEnv session) in

  let (smtEnv, session) = List.fold m.members.vars ~init:(smtEnv,session) ~f:(fun (smtEnv, session) var_def -> add_var_def var_def tbl smtEnv session) in

  
  (* let callables_list = m.members.call_defs in *)
  let callables_list = List.map m.members.call_defs 
  ~f:(fun call_def -> 
    match call_def with
    | FuncDef _func_def -> call_def
    | ProcDef proc_def -> 
      (match proc_def.proc_body with
      | None -> call_def
      | Some stmt ->
        let _atom_constr, stmt' = Callable_checker.stmt_preprocessor_simple stmt tbl in

        let proc_def = { proc_def with
          proc_body = Some stmt'
        }

        in

        ProcDef proc_def
      )
    ) in

    

  let (smtEnv, session) = 
    if m.interface then
      List.fold callables_list ~init:(smtEnv,session) ~f:(fun (smtEnv, session) callable -> 
        try
          Callable_checker.check_interface_callable callable tbl smtEnv session
        with
        | Util.Error.Msg (_loc, msg) -> 
          Stdio.prerr_endline ("---------");
          Stdio.prerr_endline "";
          Stdio.prerr_endline (Backtrace.to_string (Backtrace.Exn.most_recent ()));
          
          Util.Error.error_simple @@ Printf.sprintf " \027[31mCould not verify %s of module %s\027[0m: \n\n%s" (Ident.to_string (Callable.to_decl callable).call_decl_name) (Ident.to_string m.module_decl.mod_decl_name) msg
        )

    else 
      List.fold callables_list ~init:(smtEnv,session) ~f:(fun (smtEnv, session) callable -> 
        try
          Callable_checker.check_module_callable callable tbl smtEnv session
        with
        | Util.Error.Msg (_loc, msg) -> 
          Stdio.prerr_endline ("---------");
          Stdio.prerr_endline "";
          Stdio.prerr_endline (Backtrace.to_string (Backtrace.Exn.most_recent ()));
          
          Util.Error.error_simple @@ Printf.sprintf " \027[31mCould not verify %s of module %s\027[0m: \n\n%s" (Ident.to_string (Callable.to_decl callable).call_decl_name) (Ident.to_string m.module_decl.mod_decl_name) msg
      ) in


  let smtEnv = SmtEnv.pop_ident smtEnv in

  (smtEnv, session)

let start_backend_checking (m: Module.t) (tbl: SymbolTbl.t) = 
  let session = Smt_solver.init () in

  check_module m tbl (SmtEnv.push ([], [])) session
