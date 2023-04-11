open Smt_solver
open Ast
open Base
open Frontend.Process_ast
open SmtLibAST

let add_type (tp: Module.type_alias) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: Smt_solver.session) : (smt_env * Smt_solver.session)  =
  let fully_qualified_name = SmtEnv.mk_qual_ident smtEnv tp.type_alias_name in

  let smt_ident = SMTIdent.make (QualIdent.to_string fully_qualified_name) in

  match tp.type_alias_def with
  | None -> (
    let tp_trns = FreeSort (smt_ident, []);
    in

    let _ = Smt_solver.write session (mk_declare_sort smt_ident 0) in
    let smtEnv = SmtEnv.add smtEnv fully_qualified_name (Type tp_trns) in

    smtEnv, session
  )

  | Some tp_expr ->
    let tp_trns = Callable_checker.lookup_type tp_expr tbl smtEnv in

    (* Smt_solver.write session (mk_declare_datatype) *)

    let smtEnv = SmtEnv.add smtEnv fully_qualified_name (Type tp_trns) in
    smtEnv, session

let add_field (field: Module.field_def) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: Smt_solver.session) : (smt_env * Smt_solver.session) =
  let name_qual_ident = SmtEnv.mk_qual_ident smtEnv field.field_name in

  let fully_qualified_name = (QualIdent.to_string name_qual_ident) in

  let field_heap_ident = SMTIdent.fresh (fully_qualified_name ^"@OwnHeap") in

  let field_sort = Callable_checker.lookup_type field.field_type tbl smtEnv in
  let field_heap_term = mk_const (Ident field_heap_ident) in

  let (field_trnsl: SmtEnv.field_trnsl) = (match field.field_type with

  | App (Int, _, _) ->
    {
      field_heap = field_heap_term;
      field_sort = field_sort;
      field_heap_valid = PreambleConsts.int_frac_heap_valid_ident;
      field_heap_add_chunk = PreambleConsts.int_frac_chunk_add_ident;
      field_heap_subtract_chunk = PreambleConsts.int_frac_chunk_subtract_ident;
      heapchunk_compare = PreambleConsts.int_heapchunk_compare_ident;
    }

  | App (Bool, _, _) ->
    {
      field_heap = field_heap_term;
      field_sort = field_sort;
      field_heap_valid = PreambleConsts.bool_frac_heap_valid_ident;
      field_heap_add_chunk = PreambleConsts.bool_frac_chunk_add_ident;
      field_heap_subtract_chunk = PreambleConsts.bool_frac_chunk_subtract_ident;
      heapchunk_compare = PreambleConsts.bool_heapchunk_compare_ident;
    }

  | App (Ref, _, _) ->
    {
      field_heap = field_heap_term;
      field_sort = field_sort;
      field_heap_valid = PreambleConsts.loc_frac_heap_valid_ident;
      field_heap_add_chunk = PreambleConsts.loc_frac_chunk_add_ident;
      field_heap_subtract_chunk = PreambleConsts.loc_frac_chunk_subtract_ident;
      heapchunk_compare = PreambleConsts.loc_heapchunk_compare_ident;
    }

  | _ ->
    let field_heap_valid = SMTIdent.make (fully_qualified_name ^ "@HeapValid") in
    let field_heap_add_chunk = SMTIdent.make (fully_qualified_name ^ "@HeapAddChunk") in
    let field_heap_subtract_chunk = SMTIdent.make (fully_qualified_name ^ "@HeapSubtractChunk") in
    let heapchunk_compare = SMTIdent.make (fully_qualified_name ^ "@HeapChunkCompare") in

    let _ = add_frac_field_heap_functions field_sort field_heap_valid field_heap_add_chunk field_heap_subtract_chunk heapchunk_compare session in
    {
      field_heap = field_heap_term;
      field_sort = field_sort;
      field_heap_valid = field_heap_valid;
      field_heap_add_chunk = field_heap_add_chunk;
      field_heap_subtract_chunk = field_heap_subtract_chunk;
      heapchunk_compare = heapchunk_compare;
    })

  in

  declare_new_fieldheap field_trnsl field_heap_ident session;

  let loc_ident = SMTIdent.make "loc" in
  let loc_term = mk_const (Ident loc_ident) in
  
  let cmd = (mk_assert (mk_binder Forall [(loc_ident, PreambleConsts.loc_sort)]
    (mk_eq 
      (mk_annot (PreambleConsts.frac_heap_null) (As (mk_frac_heapchunk_sort field_sort))) 
      (mk_select field_heap_term loc_term)
    )
  )) in 

  Smt_solver.write session cmd;

  let smtEnv = SmtEnv.add smtEnv (SmtEnv.mk_qual_ident smtEnv field.field_name) (Field field_trnsl) in
  
  smtEnv, session


let add_var_def (var_def: Stmt.var_def) (tbl: SymbolTbl.t) (smtEnv: SmtEnv.t) (session: Smt_solver.session) : (SmtEnv.t * Smt_solver.session) = 
  let fully_qualified_name = (SmtEnv.stack_name smtEnv) ^ (Ident.to_string var_def.var_decl.var_name) in
  let fresh_var_name = SMTIdent.fresh fully_qualified_name in
  let fresh_var_term = mk_const (Ident fresh_var_name) in
  let var_sort = Callable_checker.lookup_type var_def.var_decl.var_type tbl smtEnv in

  Smt_solver.write session (mk_declare_const fresh_var_name var_sort);

  let smtEnv = SmtEnv.add smtEnv (SmtEnv.mk_qual_ident smtEnv var_def.var_decl.var_name) (Var {var_symbol = fresh_var_term; var_sort = var_sort}) in

  match var_def.var_init with 
  | None -> smtEnv, session
  | Some expr -> 
    let expr_trnsl = Callable_checker.translate_expr expr tbl smtEnv in

    Smt_solver.write session (mk_assert (mk_eq fresh_var_term expr_trnsl));

    smtEnv, session





let rec check_module (m: Module.t) (tbl: SymbolTbl.t) (smtEnv: SmtEnv.t) (session: Smt_solver.session) : (SmtEnv.t * Smt_solver.session) =
  let smtEnv = SmtEnv.push_ident smtEnv m.module_decl.mod_decl_name in

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
      List.fold callables_list ~init:(smtEnv,session) ~f:(fun (smtEnv, session) callable -> Callable_checker.check_interface_callable callable tbl smtEnv session)

    else 
      List.fold callables_list ~init:(smtEnv,session) ~f:(fun (smtEnv, session) callable -> Callable_checker.check_module_callable callable tbl smtEnv session) in


  let smtEnv = SmtEnv.pop_ident smtEnv in

  (smtEnv, session)

let start_backend_checking (m: Module.t) (tbl: SymbolTbl.t) = 
  let session = Smt_solver.init () in

  check_module m tbl (SmtEnv.push ([], [])) session