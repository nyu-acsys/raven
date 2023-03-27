open Smt_solver
open Ast
open Base
open Frontend.Process_ast
open SmtLibAST
open Util__Error

let rec lookup_type (tp_expr: type_expr) (tbl: SymbolTbl.t) (smtEnv: smt_env) : sort =
  match tp_expr with
  | App (Int, _, _) ->
    IntSort
  | App (Bool, _, _) ->
    BoolSort

  | App (Ref, _, _) ->
    LocSort

  | App (Var qual_ident, _, _) ->
    (match SmtEnv.find smtEnv qual_ident with
    | Some (Type tp_trns) -> tp_trns
    | Some (_) -> error (Type.to_loc tp_expr) "expected Type in smtEnv; found something else"
    | None -> error (Type.to_loc tp_expr) "expected Type in smtEnv; found nothing else"
    )

  | App (Set, [set_tp], _) -> 
    FreeSort (SMTIdent.make "Set", [lookup_type set_tp tbl smtEnv])

  | App (Map, [tp1; tp2], _) -> 
    FreeSort (SMTIdent.make "Array", [lookup_type tp1 tbl smtEnv; lookup_type tp2 tbl smtEnv])
  (* | App (Data of variant_decl list, _, _)
  | App (Unit, _, _) 
  | App (AtomicToken, _, _)
  | App (Perm, _, _)
  | App (Bot, _, _)
  | App (Any, _, _) -> () *)
  | _ -> unsupported_error (Type.to_loc tp_expr) "Unexpected type called in checker.lookup_type"

let add_type (tp: Module.type_alias) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: Smt_solver.session) : (smt_env * Smt_solver.session)  =
  let fully_qualified_name = QualIdent.make (snd smtEnv) tp.type_alias_name in

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
    let tp_trns = lookup_type tp_expr tbl smtEnv in

    let smtEnv = SmtEnv.add smtEnv fully_qualified_name (Type tp_trns) in
    smtEnv, session


let add_frac_field_heap_functions field_sort field_heap_valid field_heap_add_chunk field_heap_subtract_chunk session =
  let field_heap_sort = mk_frac_own_heap_sort field_sort in

  let heap_ident = SMTIdent.make "heap" in
  let l_ident = SMTIdent.make "l" in
  let chunk_ident = SMTIdent.make "chunk" in

  let heap_term = mk_app (Ident heap_ident) [] in
  let l_term = mk_app (Ident l_ident) [] in
  let chunk_term = mk_app (Ident chunk_ident) [] in

  let i_term = term_of_string "i" in
  let r_term = term_of_string "r" in

  let frac_chunk_top = (mk_annot (mk_const (Ident frac_heap_top)) (As (mk_frac_heapchunk_sort field_sort))) in

  Smt_solver.write session 
  (mk_declare_fun field_heap_valid [field_heap_sort] BoolSort);

  Smt_solver.write session
  (mk_assert (mk_binder Forall 
    [(heap_ident, field_heap_sort); 
    (l_ident, LocSort); 
    (chunk_ident, mk_frac_heapchunk_sort field_sort)] 
    
    (mk_impl 
        (mk_and [
          mk_app (Ident field_heap_valid) [heap_term]; 

          mk_eq (mk_select heap_term l_term) chunk_term 
        ])



        (mk_match chunk_term 
          [(mk_const (Ident frac_heap_null), mk_const (BoolConst true));
          (mk_app (Ident frac_chunk_constr) [i_term; r_term], mk_and [(mk_leq (mk_const (IntConst 0)) r_term); (mk_geq (mk_const (IntConst 1)) r_term)]);
          (mk_const (Ident frac_heap_top), mk_const (BoolConst false));
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

  Smt_solver.write session
  (mk_define_fun field_heap_add_chunk [(x1_arg, mk_frac_heapchunk_sort field_sort); (x2_arg, mk_frac_heapchunk_sort field_sort)] (mk_frac_heapchunk_sort field_sort) 
  
    (mk_match (mk_const (Ident x1_arg))
      [
        (mk_const (Ident frac_heap_null), mk_const (Ident x2_arg));
        (mk_app (Ident frac_chunk_constr) [v1_term; r1_term], 
          (mk_match (mk_const (Ident x2_arg))
            [
              (mk_const (Ident frac_heap_null), mk_const (Ident x1_arg));
              (
                mk_app (Ident frac_chunk_constr) [v2_term; r2_term],
                (mk_ite 
                  (mk_eq v1_term v2_term) 
                  (mk_app (Ident frac_chunk_constr) [v1_term; (mk_app Plus [r1_term; r2_term])])
                  frac_chunk_top
                )
              );
              (mk_const (Ident frac_heap_top), mk_const (Ident frac_heap_top));
            ]
          )
        );
        (mk_const (Ident frac_heap_top), frac_chunk_top);
      ]
    )
  );

  Smt_solver.write session
  (mk_define_fun field_heap_subtract_chunk [(x1_arg, mk_frac_heapchunk_sort field_sort); (x2_arg, mk_frac_heapchunk_sort field_sort)] (mk_frac_heapchunk_sort field_sort)

    (mk_match (mk_const (Ident x2_arg))
      [
        (mk_const (Ident frac_heap_null), mk_const (Ident x1_arg));
        (mk_app (Ident frac_chunk_constr) [v2_term; r2_term], 
          (mk_match (mk_const (Ident x1_arg))
            [
              (mk_const (Ident frac_heap_null), (mk_annot (mk_const (Ident frac_heap_top)) (As (mk_frac_heapchunk_sort field_sort))));
              (
                mk_app (Ident frac_chunk_constr) [v1_term; r1_term],
                (mk_ite (mk_eq v1_term v2_term)
                  (mk_ite (mk_eq r1_term r2_term)
                    (mk_annot (mk_const (Ident frac_heap_null)) (As (mk_frac_heapchunk_sort field_sort)))
                    (mk_ite (mk_gt r1_term r2_term)
                      (mk_app (Ident frac_chunk_constr) [v1_term; (mk_app Minus [r1_term; r2_term])])
                      frac_chunk_top
                    )
                  )
                  frac_chunk_top
                )
              );
              (mk_const (Ident frac_heap_top), frac_chunk_top);
            ]
          )
        );
        (mk_const (Ident frac_heap_top), frac_chunk_top)
      ]
    )
  );
  ()


let redefine_field_heap field_heap_ident field_sort field_heap_valid session =
  Smt_solver.write session (mk_declare_const field_heap_ident (mk_frac_own_heap_sort field_sort));
  Smt_solver.write session (mk_assert (mk_app (Ident field_heap_valid) [mk_const (Ident field_heap_ident)]));
  ()


let add_field (field: Module.field_def) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: Smt_solver.session) : (smt_env * Smt_solver.session) =
  let fully_qualified_name = (SmtEnv.stack_name smtEnv) ^ (Ident.to_string field.field_name) in

  let field_heap_ident = SMTIdent.fresh (fully_qualified_name ^ "@OwnHeap") in
  let field_sort = lookup_type field.field_type tbl smtEnv in
  let field_heap_term = mk_const (Ident field_heap_ident) in

  let (field_trnsl: SmtEnv.field_trnsl) = (match field.field_type with

  | App (Int, _, _) ->
    {
      field_heap = field_heap_term;
      field_sort = field_sort;
      field_heap_valid = SMTIdent.make "IntHeapValid";
      field_heap_add_chunk = SMTIdent.make "IntHeapAddChunk";
      field_heap_subtract_chunk = SMTIdent.make "IntHeapSubtractChunk";
    }

  | App (Bool, _, _) ->
    {
      field_heap = field_heap_term;
      field_sort = field_sort;
      field_heap_valid = SMTIdent.make "BoolHeapValid";
      field_heap_add_chunk = SMTIdent.make "BoolHeapAddChunk";
      field_heap_subtract_chunk = SMTIdent.make "BoolHeapSubtractChunk";
    }

  | App (Ref, _, _) ->
    {
      field_heap = field_heap_term;
      field_sort = field_sort;
      field_heap_valid = SMTIdent.make "LocHeapValid";
      field_heap_add_chunk = SMTIdent.make "LocHeapAddChunk";
      field_heap_subtract_chunk = SMTIdent.make "LocHeapSubtractChunk";
    }

  | _ ->
    let field_heap_valid = SMTIdent.make (fully_qualified_name ^ "@HeapValid") in
    let field_heap_add_chunk = SMTIdent.make (fully_qualified_name ^ "@HeapAddChunk") in
    let field_heap_subtract_chunk = SMTIdent.make (fully_qualified_name ^ "@HeapSubtractChunk") in

    let _ = add_frac_field_heap_functions field_sort field_heap_valid field_heap_add_chunk field_heap_subtract_chunk session in
    {
      field_heap = field_heap_term;
      field_sort = field_sort;
      field_heap_valid = field_heap_valid;
      field_heap_add_chunk = field_heap_add_chunk;
      field_heap_subtract_chunk = field_heap_subtract_chunk;
    })

  in

  redefine_field_heap field_heap_ident field_sort field_trnsl.field_heap_valid session;

  let loc_ident = SMTIdent.make "loc" in
  let loc_term = mk_const (Ident loc_ident) in
  
  let cmd = (mk_assert (mk_binder Forall [(loc_ident, loc_sort)]
    (mk_eq 
      (mk_annot (mk_const (Ident frac_heap_null)) (As (mk_frac_heapchunk_sort field_sort))) 
      (mk_select field_heap_term loc_term)
    )
  )) in 

  Smt_solver.write session cmd;

  let smtEnv = SmtEnv.add smtEnv (SmtEnv.mk_qual_ident smtEnv field.field_name) (Field field_trnsl) in
  
  smtEnv, session

let rec translate_expr (expr: Expr.t) tbl smtEnv : term =
  match expr with
  | App (constr, expr_list, expr_attr) ->
    (let smt_term_list = List.map expr_list ~f:(fun expr -> translate_expr expr tbl smtEnv) in
    (match constr with
    | Bool b -> mk_const ~pos:expr_attr.expr_loc (BoolConst b)
    | Int i -> mk_const ~pos:expr_attr.expr_loc (IntConst (Int64.to_int_exn i))
    | Not -> mk_app ~pos:expr_attr.expr_loc Not smt_term_list
    | Uminus -> mk_app ~pos:expr_attr.expr_loc Mult (mk_const (IntConst (-1)) :: smt_term_list)
    | MapLookUp -> mk_app ~pos:expr_attr.expr_loc Select smt_term_list
    | Eq -> mk_app ~pos:expr_attr.expr_loc Eq smt_term_list
    | Gt -> mk_app ~pos:expr_attr.expr_loc Gt smt_term_list
    | Lt -> mk_app ~pos:expr_attr.expr_loc Lt smt_term_list
    | Geq -> mk_app ~pos:expr_attr.expr_loc Geq smt_term_list
    | Leq -> mk_app ~pos:expr_attr.expr_loc Leq smt_term_list
    | Diff
    | Union
    | Inter
    | Elem
    | Subseteq -> unsupported_error (Expr.loc expr) "set expressions not supported presently"
    | And -> mk_app ~pos:expr_attr.expr_loc And smt_term_list
    | Or -> mk_app ~pos:expr_attr.expr_loc Or smt_term_list
    | Impl -> mk_app ~pos:expr_attr.expr_loc Impl smt_term_list
    | Plus -> mk_app ~pos:expr_attr.expr_loc Plus smt_term_list
    | Minus -> mk_app ~pos:expr_attr.expr_loc Minus smt_term_list
    | Div -> mk_app ~pos:expr_attr.expr_loc Div smt_term_list 
    | Mod -> mk_app ~pos:expr_attr.expr_loc Mod smt_term_list
    | Ite -> mk_app ~pos:expr_attr.expr_loc Ite smt_term_list
    | Call ->
      (match expr_list with
      | App (Var qual_ident, [], _) :: expr_list' ->
        (match SmtEnv.find smtEnv qual_ident with
        | Some (Func func_trnsl) ->
          let smt_term_list' = List.map expr_list' ~f:(fun expr -> translate_expr expr tbl smtEnv) in
          mk_app ~pos:expr_attr.expr_loc (Ident func_trnsl.func_symbol) smt_term_list'

        | _ -> error (Expr.loc expr) "Expected function for callable in smtEnv; found something else."
        ) 
      | _ -> error (Expr.loc expr) "Invalid call_expr found"
      )
    | Read ->
      (* Permission for the given field needs to be checked earlier; when a `var x = y.f` stmt is found. We will assume that field reads only appear when directly assigned to variables. *)
      (match expr_list with
      | [expr1; App (Var qual_ident, [], _)] ->
        (* TODO: Generalize for non-frac RAs. *)
        (match SmtEnv.find smtEnv qual_ident with
        | Some (Field field_trsnl) ->
          let term1 = translate_expr expr1 tbl smtEnv in
          mk_app (Ident frac_chunk_val) [(mk_app Select [(field_trsnl.field_heap); term1])]

        | _ -> error (Expr.loc expr) "Expected field for read_expr in smtEnv; found something else."
        )
      | _ -> error (Expr.loc expr) "Invalid read_expr found"
      )
    
    | _ -> error (Expr.loc expr) ("unsupported expr: " ^ Expr.to_string expr)

    ))
  | Binder _ -> error (Expr.loc expr) "translate_expr does not support binder expr."


let add_var_def (var_def: Stmt.var_def) (tbl: SymbolTbl.t) (smtEnv: SmtEnv.t) (session: Smt_solver.session) : (SmtEnv.t * Smt_solver.session) = 
  let fully_qualified_name = (SmtEnv.stack_name smtEnv) ^ (Ident.to_string var_def.var_decl.var_name) in
  let fresh_var_name = SMTIdent.fresh fully_qualified_name in
  let fresh_var_term = mk_const (Ident fresh_var_name) in
  let var_sort = lookup_type var_def.var_decl.var_type tbl smtEnv in

  Smt_solver.write session (mk_declare_const fresh_var_name var_sort);

  let smtEnv = SmtEnv.add smtEnv (SmtEnv.mk_qual_ident smtEnv var_def.var_decl.var_name) (Var {var_symbol = fresh_var_term; var_sort = var_sort}) in

  match var_def.var_init with 
  | None -> smtEnv, session
  | Some expr -> 
    let expr_trnsl = translate_expr expr tbl smtEnv in

    Smt_solver.write session (mk_assert (mk_eq fresh_var_term expr_trnsl));

    smtEnv, session


let rec check_stmt (stmt: Stmt.stmt_desc) (tbl: SymbolTbl.t) (smtEnv: SmtEnv.t) (session: Smt_solver.session) : (SmtEnv.t * Smt_solver.session) =
  ()

let check_basic_stmt (stmt: Stmt.basic_stmt_desc) (tbl: SymbolTbl.t) (smtEnv: SmtEnv.t) (session: Smt_solver.session) : (SmtEnv.t * Smt_solver.session) =
  match stmt with
  | VarDef var_def ->
    var_def.var_decl.var_name
  | Assume spec -> ()
  | Assert spec -> ()
  | New new_desc -> ()
  | Assign assign_desc -> ()
  | Havoc expr_list -> ()
  | Call call_desc -> ()
  | Return expr_list -> ()
  | Fold fold_desc -> ()
  | Unfold unfold_desc -> ()
  | BindAU ident -> ()
  | OpenAU ident -> ()
  | AbortAU ident -> ()
  | CommitAU ident -> ()
  | OpenInv expr -> ()
  | CloseInv expr -> ()
  | Inhale expr   -> ()
  | Exhale expr -> ()


let rec check_module (m: Module.t) (tbl: SymbolTbl.t) (smtEnv: SmtEnv.t) (session: Smt_solver.session) : (SmtEnv.t * Smt_solver.session) =
  let (smtEnv,session) = List.fold m.members.mod_defs ~init:(smtEnv,session) ~f:(fun (smtEnv,session) m -> 
    let (smtEnv', session') = check_module m tbl (SmtEnv.push_ident smtEnv m.module_decl.mod_decl_name) session in
    (SmtEnv.pop_ident smtEnv', session')
  ) in

  let (smtEnv,session) = List.fold m.members.types ~init:(smtEnv,session) ~f:(fun (smtEnv,session) tp -> add_type tp tbl smtEnv session) in

  let (smtEnv,session) = List.fold m.members.fields ~init:(smtEnv,session) ~f:(fun (smtEnv,session) field -> add_field field tbl smtEnv session) in

  let (smtEnv, session) = List.fold m.members.vars ~init:(smtEnv,session) ~f:(fun (smtEnv, session) var_def -> add_var_def var_def tbl smtEnv session) in

  
  let callables_list = m.members.call_defs in
  (* let callables_list = List.map m.members.call_defs 
  ~f:(fun call_def -> 
    match call_def with
    | FuncDef _func_def -> call_def
    | ProcDef proc_def -> 
      (match proc_def.proc_body with
      | None -> call_def
      | Some stmt ->
        let _atom_constr, stmt' = Callable_checker.CallableChecker.stmt_preprocessor_simple stmt tbl in

        let proc_def = { proc_def with
          proc_body = Some stmt'
        }

        in

        ProcDef proc_def
      )
    ) in *)

    

    let (smtEnv, session) = 
      if m.interface then   
        List.fold callables_list ~init:(smtEnv,session) ~f:(fun (smtEnv, session) callable -> Callable_checker.CallableChecker.check_interface_callable callable tbl smtEnv session)

      else 
        List.fold callables_list ~init:(smtEnv,session) ~f:(fun (smtEnv, session) callable -> Callable_checker.CallableChecker.check_module_callable callable tbl smtEnv session) in

    (smtEnv, session)

let start_backend_checking (m: Module.t) (tbl: SymbolTbl.t) = 
  let session = Smt_solver.init () in

  check_module m tbl (SmtEnv.push ([], [m.module_decl.mod_decl_name])) session