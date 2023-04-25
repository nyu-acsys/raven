
open Base
open Ast
open Util
open Frontend__Process_ast
open SmtLibAST
open Smt_solver

let rec lookup_type (tp_expr: type_expr) (tbl: SymbolTbl.t) (smtEnv: smt_env) : sort =
  match tp_expr with
  | App (Int, _, _) ->
    IntSort
  | App (Bool, _, _) ->
    BoolSort

  | App (Ref, _, _) ->
    PreambleConsts.loc_sort

  | App (Var qual_ident, _, _) ->
    (match SmtEnv.find smtEnv qual_ident with
    | Some (Type tp_trns) -> tp_trns
    | Some (_) -> Error.error (Type.to_loc tp_expr) "expected Type in smtEnv; found something else"
    | None -> Error.error (Type.to_loc tp_expr) (Printf.sprintf "lookup_type (%s) : expected Type in smtEnv; found nothing. SmtEnv: %s" (Type.to_string tp_expr) (SmtEnv.to_string smtEnv)) 
    )

  | App (Set, [set_tp], _) -> 
    FreeSort (SMTIdent.make "Set", [lookup_type set_tp tbl smtEnv])

  | App (Map, [tp1; tp2], _) -> 
    ArraySort ((lookup_type tp1 tbl smtEnv), (lookup_type tp2 tbl smtEnv))
  (* | App (Data of variant_decl list, _, _)
  | App (Unit, _, _) 
  | App (AtomicToken, _, _)
  | App (Perm, _, _)
  | App (Bot, _, _)
  | App (Any, _, _) -> () *)
  | _ -> Error.unsupported_error (Type.to_loc tp_expr) (Printf.sprintf "Unexpected type called in checker.lookup_type: %s" (Type.to_string tp_expr))




let rec translate_expr (expr: Expr.t) tbl smtEnv : term =
  match expr with
  | App (constr, expr_list, expr_attr) ->
    (let smt_term_list = List.map expr_list ~f:(fun expr -> translate_expr expr tbl smtEnv) in
    (match constr with
    | Bool b -> mk_bool ~pos:expr_attr.expr_loc b
    | Int i -> mk_int ~pos:expr_attr.expr_loc (Int64.to_int_exn i)
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
    | Subseteq -> Error.unsupported_error (Expr.loc expr) "set expressions not supported presently"
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

        | _ -> Error.error (Expr.loc expr) "Expected function for callable in smtEnv; found something else."
        ) 
      | _ -> Error.error (Expr.loc expr) "Invalid call_expr found"
      )
    | Read ->
      (* Permission for the given field needs to be checked earlier; when a `var x = y.f` stmt is found. We will assume that field reads only appear when directly assigned to variables. *)
      (* TODO: Make sure this is actually being done. *)
      (match expr_list with
      | [expr1; App (Var qual_ident, [], _)] ->
        (* TODO: Generalize for non-frac RAs. *)
        (match SmtEnv.find smtEnv qual_ident with
        | Some (Field field_trsnl) ->
          let term1 = translate_expr expr1 tbl smtEnv in
          mk_app (Ident PreambleConsts.frac_val_destr_ident) [(mk_app Select [(field_trsnl.field_heap); term1])]

        | _ -> Error.error (Expr.loc expr) "Expected field for read_expr in smtEnv; found something else."
        )
      | _ -> Error.error (Expr.loc expr) "Invalid read_expr found"
      )

    | Var qual_ident ->
      (match SmtEnv.find smtEnv qual_ident with
      | Some (Var var_trnsl) -> var_trnsl.var_symbol
      | Some (Func func_trnsl) -> 
        (* The below value should never be used. It should be intercepted by the Call case above. *)
        mk_const (Ident func_trnsl.func_symbol)
      | Some (DataConstr data_constr) -> mk_const (Ident data_constr.constr)
      | Some (DataDestr data_destr) -> mk_const (Ident data_destr.destr)
      | Some smt_trnsl -> Error.error (Expr.loc expr) @@ Printf.sprintf "Unexpected element %s found in translate_expr for expr '%s' in smtEnv." (SmtEnv.trnsl_to_string smt_trnsl) (Expr.to_string expr)
      | None -> Error.error (Expr.loc expr) @@ Printf.sprintf "Nothing found for %s from translate_expr in smtEnv. \n smtEnv: %s" (QualIdent.to_string qual_ident) (SmtEnv.to_string smtEnv)
      )
    
    | DataConstr ->
      (match expr_list with
      | App (Var qual_ident, [], _) :: expr_list' -> 
        (match SmtEnv.find smtEnv qual_ident with
        | Some (DataConstr data_constr) -> 
          let smt_term_list' = List.map expr_list' ~f:(fun expr -> translate_expr expr tbl smtEnv) in

          mk_app ~pos:expr_attr.expr_loc (Ident data_constr.constr) smt_term_list'
        | _ -> Error.error (Expr.loc expr) @@ Printf.sprintf "Unexpected element found in translate_expr for expr '%s' in smtEnv." (Expr.to_string expr))

      | _ -> Error.error (Expr.loc expr) "Invalid DataConstr expr found")
    
    | DataDestr -> 
      (match expr_list with
      | [expr1; App (Var qual_ident, [], _) ] -> 
        (match SmtEnv.find smtEnv qual_ident with
        | Some (DataDestr data_destr) -> 
          let smt_term1 = translate_expr expr1 tbl smtEnv in
            (* List.map expr_list' ~f:(fun expr -> translate_expr expr tbl smtEnv) in *)

          mk_app ~pos:expr_attr.expr_loc (Ident data_destr.destr) [smt_term1]
        | _ -> Error.error (Expr.loc expr) @@ Printf.sprintf "Unexpected element found in translate_expr for expr '%s' in smtEnv." (Expr.to_string expr))
      | _ -> Error.error (Expr.loc expr) "Invalid DataDestr expr found")
    
    | _ -> Error.error (Expr.loc expr) (Printf.sprintf "unsupported expr: %s; smtEnv = %s" (Expr.to_string expr) (SmtEnv.to_string smtEnv))

    ))
    | Binder (Forall, quant_vars, expr, _) ->
      let quant_var_sort_list = List.map quant_vars ~f:(fun var_decl -> 
        let tp = var_decl.var_type in
        let sort = lookup_type tp tbl smtEnv in
  
        (SMTIdent.fresh (Ident.to_string var_decl.var_name), sort)
        )
      in
  
      let smtEnv' = SmtEnv.push smtEnv in
      let smtEnv' = List.fold (List.zip_exn (List.map quant_vars ~f:(fun var -> QualIdent.from_ident (var.var_name))) quant_var_sort_list) ~init:smtEnv' ~f:(fun smtEnv (qual_ident, (smt_ident, sort)) -> SmtEnv.add smtEnv qual_ident (Var {var_symbol = mk_const (Ident smt_ident); var_sort = sort})) in
  
      let expr_term = try
        translate_expr expr tbl smtEnv'
      with
        Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported forall expression found in exhale: %s" (Expr.to_string expr) )
  
      in
  
      let term = 
        (mk_forall quant_var_sort_list expr_term) in
  
      term

    | Binder (Exists, quant_vars, expr, _) ->
      let quant_var_sort_list = List.map quant_vars ~f:(fun var_decl -> 
        let tp = var_decl.var_type in
        let sort = lookup_type tp tbl smtEnv in
  
        (SMTIdent.fresh (Ident.to_string var_decl.var_name), sort)
        )
      in
  
      let smtEnv' = SmtEnv.push smtEnv in
      let smtEnv' = List.fold (List.zip_exn (List.map quant_vars ~f:(fun var -> QualIdent.from_ident (var.var_name))) quant_var_sort_list) ~init:smtEnv' ~f:(fun smtEnv (qual_ident, (smt_ident, sort)) -> SmtEnv.add smtEnv qual_ident (Var {var_symbol = mk_const (Ident smt_ident); var_sort = sort})) in
  
      let expr_term = try
        translate_expr expr tbl smtEnv'
      with
        Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported Exists expression found in exhale: %s" (Expr.to_string expr) )
  
      in
  
      let term = 
        (mk_exists quant_var_sort_list expr_term) in
  
      term
    
    | Binder (Compr, _, _, _) ->
      Error.error (Expr.loc expr) "translate_expr does not support compr binder expr."

type atomicity_status = | Default | Opened | Stepped
type atomicity_constraints = {
  status : atomicity_status;
  opened_invariants : expr list;
  opened_atomic_token : ident option;
  ghost_block : bool;
}

let default_atomicity_constraint : atomicity_constraints = {
  status = Default;
  opened_invariants = [];
  opened_atomic_token = None;
  ghost_block = false;
}

let atom_step (atom_constr: atomicity_constraints) =
  match atom_constr.status with
  | Default -> atom_constr
  | Opened -> 
    (match atom_constr.ghost_block with
    | true -> atom_constr
    | false -> { atom_constr with
      status = Stepped;
      }
    )
  | Stepped -> 
    (match atom_constr.ghost_block with
    | true -> atom_constr
    | false -> raise (Error.Generic_Error "Violated Atomicity Constraints")
    )
    

let rec stmt_preprocessor (stmt: Stmt.t) (tbl: SymbolTbl.t) ~(atom_constr: atomicity_constraints) : atomicity_constraints * Stmt.t  = 
  (* This function replaces any Call() stmts with appropriate inhale and exhale statements by looking at its spec from tbl, and also tracks whether atomic constrainsts are satisfied. *)
  let open Stmt in
  let atom_const, stmt_desc = 
  (match stmt.stmt_desc with 
  | Block stmt_list ->
    let atom_const, stmt_list = List.fold_map stmt_list ~init:atom_constr ~f:(fun atom_const stmt -> stmt_preprocessor stmt tbl ~atom_constr:atom_const) in

    atom_const, Block stmt_list
  
  | Loop loop_desc ->
    let atom_constr, loop_prebody = stmt_preprocessor loop_desc.loop_prebody tbl ~atom_constr:atom_constr in
    let atom_constr, loop_postbody = stmt_preprocessor loop_desc.loop_postbody tbl ~atom_constr:atom_constr in
    
    let loop_desc = { loop_desc with
      loop_prebody;
      loop_postbody;
    } in

    atom_constr, Loop loop_desc
  
  | Cond cond_desc ->
    let cond_test = cond_desc.cond_test in
    let atom_constr, cond_then = stmt_preprocessor cond_desc.cond_then tbl ~atom_constr:atom_constr in
    let atom_constr, cond_else = stmt_preprocessor cond_desc.cond_else tbl ~atom_constr:atom_constr in

    let cond_desc = {
      cond_test;
      cond_then;
      cond_else;
    }

    in
    atom_constr, Cond cond_desc
  
  | Ghost ghost_desc ->
    let atom_constr', ghost_body = stmt_preprocessor ghost_desc.ghost_body tbl ~atom_constr:{atom_constr with ghost_block = true;} in

    let ghost_desc = { 
      ghost_body;
    }
    (* TODO: Implement Atomic Constraints for Ghost blocks correctly *)
    in
    {atom_constr' with ghost_block = false;}, Ghost ghost_desc


  | Basic basic_stmt_desc ->
    (match basic_stmt_desc with
    | VarDef _
    | Assume _
    | Assert _
    | New _
    | Assign _
    | Fpu _
    | Havoc _ ->
      (try
        (atom_step atom_constr), Basic basic_stmt_desc
      with
        Error.Generic_Error str -> Error.error stmt.stmt_loc str)

    | Call call_desc -> 
      (match SymbolTbl.find tbl call_desc.call_name with
      | Some Callable call_decl ->
        (match call_decl.call_decl_kind with
        | Proc -> (
          let formal_args_truncated, _ = List.split_n call_decl.call_decl_formals (List.length call_desc.call_args) in
          let map = List.fold (List.zip_exn formal_args_truncated call_desc.call_args) ~init:(Map.empty (module QualIdent)) ~f:(fun map (formal_arg, call_arg) -> Map.add_exn map ~key:(QualIdent.from_ident formal_arg) ~data:call_arg) in

          let exhale_list : Stmt.t list = List.map call_decl.call_decl_precond 
            ~f:(fun spec -> {stmt_desc = Basic (Exhale (Expr.alpha_renaming spec.spec_form map)); stmt_loc = stmt.stmt_loc}) in
          
          let inhale_list : Stmt.t list = List.map call_decl.call_decl_postcond 
          ~f:(fun spec -> {stmt_desc = Basic (Inhale (Expr.alpha_renaming spec.spec_form map)); stmt_loc = stmt.stmt_loc}) in

          (match atom_constr.status with
          | Default ->
            atom_constr, Block (exhale_list @ inhale_list)
            
          | Opened ->
            { atom_constr with status = Stepped}, Block (exhale_list @ inhale_list)

          | Stepped -> 
            Error.error stmt.stmt_loc "Violated atomicity constraints"
          ))

        | _ -> 
          (try
            (atom_step atom_constr), Basic basic_stmt_desc
          with
            Error.Generic_Error str -> Error.error stmt.stmt_loc str))
      | Some tp_elem -> Error.error stmt.stmt_loc ("Expected Callable in TpEnv; found " ^ SymbolTbl.typing_env_to_string tp_elem)
      | None -> Error.error stmt.stmt_loc ("Expected Callable in TpEnv; " ^ QualIdent.to_string call_desc.call_name ^ " not found. ")
      )
      

    | Return _expr_list -> 
      (match atom_constr.status with
      | Default ->
        atom_constr, Basic basic_stmt_desc
      | _ -> 
        Error.error stmt.stmt_loc ("Did not close all atomic stmts")
      )


    | Fold _
    | Unfold _ -> 
      atom_constr, Basic basic_stmt_desc

    | BindAU _ident -> 
      atom_constr, Basic basic_stmt_desc

    | OpenAU open_au -> 
      (match atom_constr.status with
      | Default -> 
        { atom_constr with status = Opened; opened_atomic_token = Some open_au}, Basic basic_stmt_desc
      | Opened ->
        (match atom_constr.opened_atomic_token with
        | None -> { atom_constr with opened_atomic_token = Some open_au}, Basic basic_stmt_desc
        | Some iden -> Error.error stmt.stmt_loc ("Cannot opened another atomic triple when " ^ Ident.to_string iden ^ " is opened")
        )
      | Stepped -> Error.error stmt.stmt_loc ("Cannot open another atomic triple; first close previous atomic stmts.")
      )

    | AbortAU ident 
    | CommitAU ident -> 
      (match atom_constr.status with
      | Default -> Error.error stmt.stmt_loc "Error.error: Cannot abortAU since nothing is open"
      | Opened
      | Stepped ->
        (match atom_constr.opened_atomic_token with
        | None -> Error.error stmt.stmt_loc "Error.error: Cannot abortAU since no Atomic Token is open"
        | Some ident' -> 
          if Ident.compare ident ident' = 0 then 
            (match atom_constr.opened_invariants with
            | [] -> default_atomicity_constraint, Basic basic_stmt_desc
            | _inv_list -> { atom_constr with opened_atomic_token = None}, Basic basic_stmt_desc
            )
          else
            Error.error stmt.stmt_loc ("Cannot AbortAU as " ^ Ident.to_string ident' ^ " AU is open")
        )
      
      )

    | OpenInv expr -> 
      (match atom_constr.status with
      | Default
      | Opened ->
        { atom_constr with status = Opened; opened_invariants = expr :: atom_constr.opened_invariants}, Basic basic_stmt_desc
      | Stepped ->
        { atom_constr with opened_invariants = expr :: atom_constr.opened_invariants}, Basic basic_stmt_desc
      )

    | CloseInv expr ->
      (match atom_constr.status with
      | Default -> Error.error stmt.stmt_loc "Cannot CloseInv, nothing opened."
      | Opened 
      | Stepped ->
        (match atom_constr.opened_invariants with
        | [] -> Error.error stmt.stmt_loc "Cannot CloseInv. Invariant not found."
        | [expr'] -> 
          if Expr.compare expr expr' = 0 then
            (match atom_constr.opened_atomic_token with
            | None -> default_atomicity_constraint, Basic basic_stmt_desc
            | Some _ -> {atom_constr with opened_invariants = []}, Basic basic_stmt_desc
            )
          else
            Error.error stmt.stmt_loc "Cannot CloseInv; invariants need to be closed in reverse order of opening"

        | expr' :: expr_list ->
          if Expr.compare expr expr' = 0 then
            {atom_constr with opened_invariants = expr_list}, Basic basic_stmt_desc
          else
            Error.error stmt.stmt_loc "Cannot CloseInv; invariants need to be closed in reverse order of opening"
        )
      )


    | Inhale _ 
    | Exhale _ -> 
      Error.error stmt.stmt_loc "Inhale/Exhale stmt not expected in AST at this stage."
    )


  ) in
    
  atom_const, {stmt_desc = stmt_desc; stmt_loc = stmt.stmt_loc}


let update_env (smtEnv: smt_env) (new_vars: (qual_ident * smt_ident) list) : smt_env = 
  let new_vars_map = List.fold new_vars ~init: (Map.empty (module QualIdent)) ~f:(fun map (quant_iden, smt_ident) ->
    match Map.find map quant_iden with
    | None -> Map.add_exn map ~key:quant_iden ~data:smt_ident
    | Some smt_ident' ->
      if smt_ident'.ident_num >= smt_ident.ident_num then
        map
      else
        Map.set map ~key:quant_iden ~data:smt_ident
  ) in

  let smtEnv = List.fold (Map.to_alist new_vars_map) ~init:smtEnv ~f:(fun env (qual_iden, smt_iden) ->
    match SmtEnv.find env qual_iden with
    | None -> Error.error_simple @@ Printf.sprintf "update_env called with new variable '%s'; not found in present env. smtEnv: %s" (QualIdent.to_string qual_iden) (SmtEnv.to_string smtEnv)
    | Some (Field field_trnsl) -> 
      let new_field_trnsl = { field_trnsl with
        field_heap = mk_const (Ident smt_iden);
      } in
      SmtEnv.add env qual_iden (Field new_field_trnsl)
    | Some (Var var_trnsl) ->
      let new_var_trnsl = { var_trnsl with
        var_symbol = mk_const (Ident smt_iden);
      } in
      SmtEnv.add env qual_iden (Var new_var_trnsl)
    | Some (Pred pred_trnsl) ->
      let new_pred_trnsl = { pred_trnsl with
        pred_heap = mk_const (Ident smt_iden);
      } in
      SmtEnv.add env qual_iden (Pred new_pred_trnsl)
    | _ -> Error.error_simple "update_env called with func/type; not expected to update these."
  ) in

  smtEnv

let new_vars_unify (new_vars1: (qual_ident * smt_ident) list) (new_vars2: (qual_ident * smt_ident) list) : (qual_ident * smt_ident) list =
  let new_vars_map = List.fold (new_vars1 @ new_vars2) ~init: (Map.empty (module QualIdent)) ~f:(fun map (quant_iden, smt_ident) ->
    match Map.find map quant_iden with
    | None -> Map.add_exn map ~key:quant_iden ~data:smt_ident
    | Some smt_ident' ->
      if smt_ident'.ident_num >= smt_ident.ident_num then
        map
      else
        Map.set map ~key:quant_iden ~data:smt_ident
  ) in

  let new_new_vars = List.map (Map.to_alist new_vars_map) ~f:(fun (qual_ident, smt_ident) -> (qual_ident, SMTIdent.fresh smt_ident.ident_name))

  in

  new_new_vars
  


let rec check_sep_star_injectivity (expr: expr) (tbl: SymbolTbl.t) (smtEnv: smt_env) : unit = 
  (* TODO: Implement this *)
  match expr with
  | App (And, [expr1; expr2], _) ->
    check_sep_star_injectivity expr1 tbl smtEnv;
    check_sep_star_injectivity expr2 tbl smtEnv

  | App (Ite, [_expr0; expr1; expr2], _) ->
    check_sep_star_injectivity expr1 tbl smtEnv;
    check_sep_star_injectivity expr2 tbl smtEnv

  | Binder (Forall, _quant_vars, App (Own, [_loc_expr; (App (Var _field_heap, [], _expr_attr0)); _val_expr; _frac_expr], _), _) -> ()

  | Binder (Forall, _quant_vars, 
    App (Impl, [_expr0; 
      App (Own, [_loc_expr; (App (Var _field_heap, [], _)); _val_expr; _frac_expr], _)], _
    ), _
  ) -> ()

  | Binder (Forall, _quant_vars, App (Call, (App (Var _pred_name, [], _expr_attr0)) :: _args_list, _), _) -> ()

  | _ -> ()


let touched_vars (stmt: Stmt.t) : qual_ident list =
  let rec touched_vars_helper (stmt: Stmt.t) (touched_var_list: qual_ident list) (local_var_list: qual_ident list) = (
    match stmt.stmt_desc with
    | Block stmt_list -> (List.fold stmt_list ~init:(touched_var_list, local_var_list) ~f:(fun (t_v, l_v) stmt -> touched_vars_helper stmt t_v l_v))
    | Basic basic_stmt -> (match basic_stmt with
      | VarDef var_def -> touched_var_list, (QualIdent.from_ident var_def.var_decl.var_name) :: local_var_list
      | Assign assign_desc ->
        (try 
          List.map assign_desc.assign_lhs ~f:(ASTUtil.expr_to_qual_ident) @ touched_var_list, local_var_list
        with
          | Error.Msg(_loc,_msg) -> touched_var_list, local_var_list   
            (* Error.error loc (Printf.sprintf "Assign_desc found with invalid lhs '%s'; expected list of qual_ident: '%s' " ()msg) *)
        )

      | Call call_desc -> (call_desc.call_lhs) @ touched_var_list, local_var_list

      | _ -> touched_var_list, local_var_list
    
      )


    | Loop loop_desc ->
      let t_v, l_v = touched_vars_helper loop_desc.loop_prebody touched_var_list local_var_list in
      touched_vars_helper loop_desc.loop_postbody t_v l_v
    | Cond cond_desc ->
      let t_v, l_v = touched_vars_helper cond_desc.cond_then touched_var_list local_var_list in
      touched_vars_helper cond_desc.cond_else t_v l_v

    | Ghost ghost_desc -> touched_vars_helper ghost_desc.ghost_body touched_var_list local_var_list
  )

  in

  let touched_vars_list, local_var_list = touched_vars_helper stmt [] [] in

  List.filter touched_vars_list ~f:(fun qual_ident -> not (List.exists local_var_list ~f:(QualIdent.equal qual_ident)))


let unify_conditional_branches (map1: SmtEnv.smt_trnsl qual_ident_map) (map2: SmtEnv.smt_trnsl qual_ident_map) (smt_env: smt_env) : (qual_ident * smt_ident) list =

  let new_vars_map = Map.merge_skewed map1 map2 ~combine:(fun ~key:_key val1 _val2 -> val1) in

  let new_vars_smt_ident_map = Map.map new_vars_map ~f:(fun smt_trnsl ->
    match smt_trnsl with
    | Field field_trnsl -> smt_ident_of_term field_trnsl.field_heap
    | Pred pred_trnsl -> smt_ident_of_term pred_trnsl.pred_heap
    | Var var_trnsl -> smt_ident_of_term var_trnsl.var_symbol
    | _ -> Error.error_simple "if_branches should not redefine types or functions. Error."
    ) in

  let new_new_vars = List.filter_map (Map.to_alist new_vars_smt_ident_map) ~f:(fun (qual_ident, smt_ident) -> 
    (match SmtEnv.find smt_env qual_ident with
    | None -> None
    | Some _ -> Some (qual_ident, SMTIdent.fresh smt_ident.ident_name)
    )
    ) in

  new_new_vars


let redefine_vars (new_vars: (qual_ident * smt_ident) list) (smtEnv: smt_env) (session: Smt_solver.session) : (smt_env * Smt_solver.session) = 
  let _ = List.map new_vars ~f:(fun (elem, new_name) ->
    (match SmtEnv.find smtEnv elem with
    | Some (Field field_trnsl) -> declare_new_fieldheap field_trnsl new_name session
    | Some (Pred pred_trnsl) -> declare_new_predheap pred_trnsl new_name session
    | Some (Var var_trnsl) ->
      Smt_solver.write session (mk_declare_const new_name var_trnsl.var_sort)
    | Some _ -> Error.error_simple "Redefine_vars found unexpected elem in smtEnv; expected field, pred, or var."
    | None  -> Error.error_simple @@ Printf.sprintf "Redefine_vars did not find elem '%s' in smtEnv. Error." (QualIdent.to_string elem))
  ) in

  let smtEnv = update_env smtEnv new_vars in

  smtEnv, session


let reset_all_heaps (smtEnv: smt_env) (session: Smt_solver.session) : (smt_env * Smt_solver.session) = 
  let mp = SmtEnv.flatten_env smtEnv in

  let smtEnv = Map.fold mp ~init:smtEnv ~f:(fun ~key ~data smtEnv  ->
    (match data with
    | Field field_trnsl ->

      let new_field_heap_name = SMTIdent.fresh (smt_ident_of_term field_trnsl.field_heap).ident_name in
      let new_field_heap_term = mk_const (Ident new_field_heap_name) in

      declare_new_fieldheap field_trnsl new_field_heap_name session;

      let loc_ident = SMTIdent.fresh "l" in
      let loc_term = mk_const (Ident loc_ident) in
      let cmd = (mk_assert (mk_binder Forall [(loc_ident, PreambleConsts.loc_sort)]
        (mk_eq 
          (mk_annot (PreambleConsts.frac_heap_null) (As field_trnsl.field_sort)) 
          (mk_select new_field_heap_term loc_term)
        )
      )) in 
  
      Smt_solver.write session cmd;

      let smtEnv = SmtEnv.add smtEnv key (Field {field_trnsl with field_heap = new_field_heap_term}) in

      smtEnv

    | Pred pred_trnsl ->
      let new_pred_heap_name = SMTIdent.fresh (smt_ident_of_term pred_trnsl.pred_heap).ident_name in
      let new_pred_heap_term = mk_const (Ident new_pred_heap_name) in

      declare_new_predheap pred_trnsl new_pred_heap_name session;

      let index_ident = SMTIdent.make "$index" in
      let index_term = mk_const (Ident index_ident) in
    
      let cmd = (mk_assert (mk_forall [index_ident, pred_trnsl.pred_sort]
        (mk_eq (mk_select new_pred_heap_term index_term) (mk_const (IntConst 0)))
      )) in

      Smt_solver.write session cmd;

      let smtEnv = SmtEnv.add smtEnv key (Pred {pred_trnsl with pred_heap = new_pred_heap_term}) in

      smtEnv

    | _ -> smtEnv


    )   
  ) in

  smtEnv, session

let stmt_preprocessor_simple (stmt: Stmt.t) (tbl: SymbolTbl.t) : atomicity_constraints * Stmt.t = stmt_preprocessor stmt tbl ~atom_constr:default_atomicity_constraint

let rec check_stmt (stmt: Stmt.t) (path_conds:term list) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: Smt_solver.session) : (smt_env * Smt_solver.session) =
  (match stmt.stmt_desc with
  | Block stmt_list ->
    let (smtEnv, session) = List.fold stmt_list ~init:(smtEnv, session) ~f:(fun (smtEnv, session) stmt -> check_stmt stmt path_conds tbl smtEnv session) in

    smtEnv, session

  | Basic basic_stmt -> 
      check_basic_stmt basic_stmt path_conds tbl smtEnv session (stmt.stmt_loc)
      (* smtEnv, session *)

  | Loop loop_desc ->
    (* TODO: Figure out what to do with loop_prebody here. Is the prebody even being populated by the parser? *)

    Smt_solver.write_comment session "Exhaling loop invariants in current state\n";
    (let (smtEnv, session) = List.fold loop_desc.loop_contract ~init:(smtEnv, session) ~f:(fun (smtEnv, session) spec -> 
      check_stmt ({stmt_desc = Basic (Exhale spec.spec_form); stmt_loc = stmt.stmt_loc}) path_conds tbl smtEnv session 
    ) in

    let (modified_var_list: qual_ident list) = touched_vars loop_desc.loop_postbody in

    let (modified_expr_list: expr list) = List.map modified_var_list ~f:(fun qual_ident -> Expr.mk_app (Var qual_ident) []) in

    Smt_solver.write_comment session "Havoc-ing loop vars\n";
    let (smtEnv, session) = check_basic_stmt (Havoc modified_expr_list) path_conds tbl smtEnv session (stmt.stmt_loc) in

    Smt_solver.write_comment session "Checking loop\n";
    let session = Smt_solver.push session in
    let smtEnv = SmtEnv.push smtEnv in

      Smt_solver.write_comment session "Resetting all heaps\n";
      let smtEnv, session = reset_all_heaps smtEnv session in

      Smt_solver.write_comment session "Inhaling invariants inside loop";

      let (smtEnv, session) = List.fold loop_desc.loop_contract ~init:(smtEnv, session) ~f:(fun (smtEnv, session) spec -> 
        check_stmt ({stmt_desc = Basic (Inhale spec.spec_form); stmt_loc = stmt.stmt_loc}) path_conds tbl smtEnv session 
      ) in

      Smt_solver.write session (mk_assert (translate_expr loop_desc.loop_test tbl smtEnv));
      let smtEnv', session = check_stmt loop_desc.loop_postbody (path_conds) tbl smtEnv session in

      let (_smtEnv', session) = List.fold loop_desc.loop_contract ~init:(smtEnv', session) ~f:(fun (smtEnv', session) spec -> 
        check_stmt ({stmt_desc = Basic (Exhale spec.spec_form); stmt_loc = stmt.stmt_loc}) path_conds tbl smtEnv' session 
      ) in

    let smtEnv = SmtEnv.pop smtEnv in
    let session = Smt_solver.pop session in

    Smt_solver.write_comment session "Inhaling invariants with havoc-ed variables\n";
    let (smtEnv, session) = List.fold loop_desc.loop_contract ~init:(smtEnv, session) ~f:(fun (smtEnv, session) spec -> 
      check_stmt ({stmt_desc = Basic (Inhale spec.spec_form); stmt_loc = stmt.stmt_loc}) path_conds tbl smtEnv session 
    ) in

    Smt_solver.write session (mk_assert (mk_not (translate_expr loop_desc.loop_test tbl smtEnv)));

    (smtEnv, session)
  )

  | Cond cond_desc ->
    let cond_term = translate_expr cond_desc.cond_test tbl smtEnv in

    let smtEnv1, session = check_stmt cond_desc.cond_then (cond_term :: path_conds) tbl (SmtEnv.push smtEnv) session in

    let smtEnv2, session = check_stmt cond_desc.cond_else (mk_not cond_term :: path_conds) tbl (SmtEnv.push smtEnv) session in

    let new_vars = unify_conditional_branches (List.hd_exn (fst smtEnv1)) (List.hd_exn (fst smtEnv2)) smtEnv in

    Smt_solver.write_comment session "Unifying conditional branches\n";
    let smtEnv, session = 
      try 
        redefine_vars new_vars smtEnv session 
      with
      | Error.Msg (_loc, msg) -> Error.error (stmt.stmt_loc) (Printf.sprintf "%s: redefine_vars failed" msg)
    in

    let _ = List.map new_vars ~f:(fun (qual_ident, smt_ident) ->
      let if_branch_term = (SmtEnv.find_term_exn smtEnv1 qual_ident) in
      let else_branch_term = (SmtEnv.find_term_exn smtEnv2 qual_ident) in

      let new_term = mk_const (Ident smt_ident) in

      Smt_solver.write session (mk_assert (mk_impl cond_term (mk_eq if_branch_term new_term)));
      Smt_solver.write session (mk_assert (mk_impl (mk_not cond_term) (mk_eq else_branch_term new_term)));        
      ()
      ) in

    Smt_solver.write_comment session "Finished unifying conditional branches\n";

    smtEnv, session

  | Ghost ghost_desc -> 
    check_stmt ghost_desc.ghost_body path_conds tbl smtEnv session
  
  )

and check_basic_stmt (stmt: Stmt.basic_stmt_desc) (path_conds: term list) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: Smt_solver.session) (loc: Util.Loc.t): (smt_env * Smt_solver.session) =
  match stmt with
  | VarDef var_def ->
    let fresh_var_name = SMTIdent.fresh (Ident.to_string var_def.var_decl.var_name) in
    let fresh_var_term = mk_const (Ident fresh_var_name) in
    let var_sort = lookup_type var_def.var_decl.var_type tbl smtEnv in

    Smt_solver.write session (mk_declare_const fresh_var_name var_sort);

    let smtEnv = SmtEnv.add smtEnv (QualIdent.from_ident var_def.var_decl.var_name) (Var {var_symbol = fresh_var_term; var_sort = var_sort}) in

    (match var_def.var_init with 
    | None -> smtEnv, session
    | Some _ -> 
      Error.error loc "var_defs should not have any expr (this should be unfolded earlier)."
    )

  | Assume _spec -> Error.error loc "Assume stmts not supported presently"

  | Assert spec ->
    let session = Smt_solver.push session in
      let (_, session) = check_basic_stmt (Exhale spec.spec_form) path_conds tbl smtEnv session loc in
    let session = Smt_solver.pop session in
    (*  *)
    
    smtEnv, session

  | New _new_desc -> Error.error loc "New stmts not supported presently"

  | Assign assign_desc ->
    (match assign_desc.assign_lhs with
    | [App (Var qual_ident, [], _)] -> 
      let fresh_var_name = SMTIdent.fresh (QualIdent.to_string qual_ident) in
      let fresh_var_term = mk_const (Ident fresh_var_name) in
      let var_sort = 
        (match SmtEnv.find smtEnv qual_ident with
        | Some (Var var_trnsl) -> var_trnsl.var_sort
        | Some trnsl -> Error.error loc (Printf.sprintf "Expected lhs_variable '%s' to be Var in smtEnv: found %s.\nsmtEnv = %s" (QualIdent.to_string qual_ident) (SmtEnv.trnsl_to_string trnsl) (SmtEnv.to_string smtEnv))
        | None -> Error.error loc (Printf.sprintf "Cannot find lhs_variable '%s' in smtEnv. \nsmtEnv = \n%s" (QualIdent.to_string qual_ident) (SmtEnv.to_string smtEnv))
        )
      in

      Smt_solver.write session (mk_declare_const fresh_var_name var_sort);

      let smtEnv = SmtEnv.add smtEnv qual_ident (Var {var_symbol = fresh_var_term; var_sort = var_sort}) in

      let rhs_term, session = trnsl_assign_rhs assign_desc.assign_rhs tbl smtEnv session loc

      in
      
      Smt_solver.write session (mk_assert (mk_eq fresh_var_term rhs_term));

      smtEnv, session
    
    | [App (MapLookUp, [expr1; expr2], _)] -> 
      let map_qual_ident = ASTUtil.expr_to_qual_ident expr1 in
      let fresh_map_name = SMTIdent.fresh (QualIdent.to_string map_qual_ident) in
      let fresh_map_term = mk_const (Ident fresh_map_name) in
      let old_map_term, map_sort =
        (match SmtEnv.find smtEnv map_qual_ident with
        | Some (Var var_trnsl) -> var_trnsl.var_symbol, var_trnsl.var_sort
        | Some trnsl -> Error.error loc (Printf.sprintf "Expected lhs_variable '%s' to be Var in smtEnv: found %s.\nsmtEnv = %s" (QualIdent.to_string map_qual_ident) (SmtEnv.trnsl_to_string trnsl) (SmtEnv.to_string smtEnv))
        | None -> Error.error loc (Printf.sprintf "Cannot find lhs_variable '%s' in smtEnv. \nsmtEnv = \n%s" (QualIdent.to_string map_qual_ident) (SmtEnv.to_string smtEnv))
        )
      
      in

      let rhs_term, session = trnsl_assign_rhs assign_desc.assign_rhs tbl smtEnv session loc in

      let map_source_sort, _map_dest_sort = (match map_sort with
      | ArraySort (s1, s2) -> s1, s2
      | _ -> Error.error loc (Printf.sprintf "Expected Array/Map sort for lhs_variable '%s' in smtEnv. \n smtEnv = \n%s" (QualIdent.to_string map_qual_ident) (SmtEnv.to_string smtEnv))
      ) in

      Smt_solver.write session (mk_declare_const fresh_map_name map_sort);

      let smtEnv = SmtEnv.add smtEnv map_qual_ident (Var {var_symbol = fresh_map_term; var_sort = map_sort}) in

      let map_val_term = translate_expr expr2 tbl smtEnv in

      let index_ident = SMTIdent.fresh "index" in
      let index_term = mk_const (Ident index_ident) in
      
      Smt_solver.write session (mk_assert 
        (mk_forall [(index_ident, map_source_sort)]
          (mk_ite (mk_eq index_term map_val_term) 
            (mk_eq (mk_select fresh_map_term index_term) rhs_term)
            (mk_eq (mk_select fresh_map_term index_term) (mk_select old_map_term index_term))
          )
        ));

      smtEnv, session

    | [App (Read, [expr1; expr2], _)] -> 
      let field_name = ASTUtil.expr_to_qual_ident expr2 in

      let field_trnsl = (match SmtEnv.find smtEnv field_name with
      | Some (Field field_trnsl) -> field_trnsl
      | Some trnsl -> Error.error loc (Printf.sprintf "Expected '%s' to be Field in smtEnv: found %s.\nsmtEnv = %s" (QualIdent.to_string field_name) (SmtEnv.trnsl_to_string trnsl) (SmtEnv.to_string smtEnv))
        | None -> Error.error loc (Printf.sprintf "Cannot find variable '%s' in smtEnv. \nsmtEnv = \n%s" (QualIdent.to_string field_name) (SmtEnv.to_string smtEnv))
      ) in

      let old_fieldheap_term = field_trnsl.field_heap in

      let loc_term = translate_expr expr1 tbl smtEnv in

      Smt_solver.write_comment session "Checking field write permission\n";

      let session = Smt_solver.assert_not session (
        mk_leq 
          (mk_int 1) 
          (mk_app (Ident PreambleConsts.frac_val_destr_ident) [(mk_select field_trnsl.field_heap loc_term)])
      ) in

      let rhs_term, session = trnsl_assign_rhs assign_desc.assign_rhs tbl smtEnv session loc in

      let rhs_fracchunk_term = mk_app (Ident PreambleConsts.frac_chunk_constr_ident) [rhs_term; mk_int 1] in

      Smt_solver.write_comment session "Redefing field heap";

      let new_field_heap_name = SMTIdent.fresh (smt_ident_of_term field_trnsl.field_heap).ident_name in

      let new_field_heap_term = mk_const (Ident new_field_heap_name) in

      declare_new_fieldheap field_trnsl new_field_heap_name session;

      let smtEnv = SmtEnv.add smtEnv field_name (Field {field_trnsl with field_heap = new_field_heap_term}) in

      

      let index_ident = SMTIdent.fresh "index" in
      let index_term = mk_const (Ident index_ident) in

      Smt_solver.write session (mk_assert 
        (mk_forall [(index_ident, PreambleConsts.loc_sort)]
          (mk_ite (mk_eq index_term loc_term) 
            (mk_eq (mk_select new_field_heap_term index_term) rhs_fracchunk_term)
            (mk_eq (mk_select new_field_heap_term index_term) (mk_select old_fieldheap_term index_term))
          )
        ));

      (smtEnv, session)

    | [expr] -> Error.unsupported_error loc @@ Printf.sprintf "Assign stmt found with unsupported lhs: %s" (Expr.to_string expr)

    | []
    | _ :: _ :: _ -> Error.unsupported_error loc "Assign stmt with multiple lhs not supported presently.")

  | Havoc expr_list -> 
    List.fold expr_list ~init:(smtEnv, session) ~f:(fun (smtEnv, session) expr ->
      let qual_iden = try
        ASTUtil.expr_to_qual_ident expr 
        with
          Error.Msg (loc, _msg) -> Error.error loc ("Havoc called on invalid term; only expected qual_idents. Found: " ^ (Expr.to_string expr))
      in
      let term = 
        try
          SmtEnv.find_term_exn smtEnv qual_iden
        with
        Error.Msg (loc, msg) -> Error.error loc ("Havoc term not of expected type in smtEnv: " ^ msg)


      in

      let new_smt_iden = SMTIdent.fresh (smt_ident_of_term term).ident_name in

      let smtEnv, session = redefine_vars [(qual_iden, new_smt_iden)] smtEnv session in

    smtEnv, session)

  | Call call_desc ->

    (match SmtEnv.find smtEnv call_desc.call_name with
    | Some (Func func_trnsl) -> 
      (match call_desc.call_lhs with
      | [qual_ident] ->
        let fresh_var_name = SMTIdent.fresh (QualIdent.to_string qual_ident) in
        let fresh_var_term = mk_const (Ident fresh_var_name) in
        let var_sort = 
          (match SmtEnv.find smtEnv qual_ident with
          | Some (Var var_trnsl) -> var_trnsl.var_sort
          | _ -> Error.error loc "Cannot find lhs_variable in smtEnv"
          )
        in

        Smt_solver.write session (mk_declare_const fresh_var_name var_sort);

        let smtEnv = SmtEnv.add smtEnv qual_ident (Var {var_symbol = fresh_var_term; var_sort = var_sort}) in

        let call_args_terms = List.map call_desc.call_args ~f:(fun expr -> translate_expr expr tbl smtEnv) in
        let rhs_term = mk_app (Ident func_trnsl.func_symbol) call_args_terms in

        Smt_solver.write session (mk_assert (mk_eq fresh_var_term rhs_term));

        smtEnv, session
      | _ -> Error.error loc "Unsupported lhs for function call."
      )

    | _ -> Error.error loc "Expected function in smtEnv; not found."
    )
  | Return _expr_list -> Error.unsupported_error loc "Return stmts not presently supported"
  | Fold fold_desc ->
    (* TODO: Make sure implicit ghost args are being handled correctly. *)
    (match fold_desc.fold_expr with
    | App (Call, (App (Var qual_ident, [], _)) :: args, _) -> (
      match SmtEnv.find smtEnv qual_ident with
      | Some (Pred pred_trnsl) ->
        (
          let formal_args_truncated, _ = List.split_n pred_trnsl.pred_def.func_decl.call_decl_formals (List.length args) in
          let map = List.fold (List.zip_exn formal_args_truncated args) ~init:(Map.empty (module QualIdent)) ~f:(fun map (formal_arg, call_arg) -> Map.add_exn map ~key:(QualIdent.from_ident formal_arg) ~data:call_arg) in

          let pred_body = Expr.alpha_renaming (Option.value_exn pred_trnsl.pred_def.func_body) map in

          Smt_solver.write_comment session "Exhaling body of predicate";
          let smtEnv, session = check_basic_stmt (Exhale pred_body) path_conds tbl smtEnv session loc in

          let smtEnv, session = check_basic_stmt (Inhale fold_desc.fold_expr) path_conds tbl smtEnv session loc in

          smtEnv, session
        )
      | _ -> Error.error (Expr.loc fold_desc.fold_expr) "Predicate not found in smtEnv."
    )
    | _ -> Error.unsupported_error (Expr.loc fold_desc.fold_expr) "Unsupported expr found in Fold command")
  | Unfold unfold_desc ->
    (* TODO: Make sure implicit ghost args are being handled correctly. *)
    (match unfold_desc.unfold_expr with
    | App (Call, (App (Var qual_ident, [], _)) :: args, _) -> (
      match SmtEnv.find smtEnv qual_ident with
      | Some (Pred pred_trnsl) ->
        (
          let formal_args_truncated, _ = List.split_n pred_trnsl.pred_def.func_decl.call_decl_formals (List.length args) in
          let map = List.fold (List.zip_exn formal_args_truncated args) ~init:(Map.empty (module QualIdent)) ~f:(fun map (formal_arg, call_arg) -> Map.add_exn map ~key:(QualIdent.from_ident formal_arg) ~data:call_arg) in

          let pred_body = Expr.alpha_renaming (Option.value_exn pred_trnsl.pred_def.func_body) map in

          let smtEnv, session = check_basic_stmt (Exhale unfold_desc.unfold_expr) path_conds tbl smtEnv session loc in

          let smtEnv, session = check_basic_stmt (Inhale pred_body) path_conds tbl smtEnv session loc in

          smtEnv, session
        )
      | _ -> Error.error (Expr.loc unfold_desc.unfold_expr) "Predicate not found in smtEnv."
    )
    | _ -> Error.unsupported_error (Expr.loc unfold_desc.unfold_expr) "Unsupported expr found in Unfold command")
  | BindAU _
  | OpenAU _
  | AbortAU _
  | CommitAU _
  | OpenInv _
  | CloseInv _ -> Error.unsupported_error (Loc.dummy) "AtomicToken commands not supported presently."
  | Inhale expr -> 
    check_sep_star_injectivity expr tbl smtEnv;

    let new_vars, cmds = trnsl_inhale expr tbl smtEnv in

    let smtEnv, session = redefine_vars new_vars smtEnv session in
      
    let _ = List.map (cmds) ~f:(Smt_solver.write session) in

    let smtEnv = update_env smtEnv new_vars in

    smtEnv, session

  | Exhale expr ->
    check_sep_star_injectivity expr tbl smtEnv;

    let new_vars, cmds, perm_terms = trnsl_exhale expr tbl smtEnv in

    let smtEnv, session = redefine_vars new_vars smtEnv session in

    let path_cond_term = mk_and path_conds in

    let session = List.fold perm_terms ~init:session ~f:(fun session term -> 
      let session = 
        try
          match path_conds with
          | [] -> assert_not session term
          | _ -> assert_not session (mk_impl path_cond_term term)
        (* assert_not makes sure all perm_terms are successful by asserting them under negation and checking unsat. *)
        with
          Error.Msg (_loc, _msg) -> Error.error (Expr.loc expr) (Printf.sprintf "Exhaling following expr failed:\n%s\n\nSpecifically, could not exhale: \n%s" (Expr.to_string expr) (Util.Print.string_of_format pr_term term))

      in
      
      session
    ) in

    (* This won't work in general. For instance if we exhale `(pred(a) && pred(a))` this will cause an error because predHeap is not being defined after exhaling first copy of pred(a), before the constraint on it is checked. *)

    List.iter (cmds) ~f:(Smt_solver.write session);

    let smtEnv = update_env smtEnv new_vars in

    smtEnv, session

  | Fpu fpu_desc ->
    match (SmtEnv.find smtEnv fpu_desc.fpu_field), (SmtEnv.find smtEnv fpu_desc.fpu_loc) with
    | Some (Field field_trnsl), Some (Var var_trnsl) ->

      let val_term = translate_expr fpu_desc.fpu_val tbl smtEnv in
      let loc_term = var_trnsl.var_symbol in
      let field_fpu = (match field_trnsl.field_fpu with
      | Some iden -> iden
      | None -> Error.error loc @@ Printf.sprintf "fpuApply not found for field fpu"
      ) in
      let perm_term = mk_app (Ident field_fpu) [mk_select field_trnsl.field_heap loc_term; val_term] in
      let session = assert_not session perm_term in

      let old_fieldheap_term = field_trnsl.field_heap in
      let old_fieldheap = smt_ident_of_term old_fieldheap_term in
      let new_fieldheap = SMTIdent.fresh old_fieldheap.ident_name in
      let new_fieldheap_term = mk_const (Ident new_fieldheap) in

      let smtEnv, session = redefine_vars [(fpu_desc.fpu_field, new_fieldheap)] smtEnv session in
      
      let l_ident = SMTIdent.make "l" in
      let l_term = mk_const (Ident l_ident) in
      let cmd = 
        mk_assert (mk_binder Forall [(l_ident, PreambleConsts.loc_sort)] 
          (mk_ite (mk_eq l_term loc_term)
            (mk_eq (mk_select new_fieldheap_term l_term) val_term)
            (mk_eq (mk_select new_fieldheap_term l_term) (mk_select old_fieldheap_term l_term))
          )
        ) in

      Smt_solver.write session cmd;

      smtEnv, session

    | _ -> Error.error loc @@ Printf.sprintf "Field %s or loc %s for fpu not found in smtEnv" (QualIdent.to_string fpu_desc.fpu_field) (QualIdent.to_string fpu_desc.fpu_loc)





and trnsl_assign_rhs (expr: expr) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: session) (loc: Loc.t) : term * session =
  (* Makes sure the correct read permissions exist for field reads. *)
  (match expr with
    | App (Read, expr_list, _) ->
      (match expr_list with
      | [expr1; App (Var qual_ident, [], _)] ->
        (* TODO: Generalize for non-frac RAs. *)
        (match SmtEnv.find smtEnv qual_ident with
        | Some (Field field_trsnl) ->
          let term1 = translate_expr expr1 tbl smtEnv in

          Smt_solver.write_comment session "Checking field read permission\n";
          let session = 
            try 
              Smt_solver.assert_not session 
              (mk_lt 
                (mk_const (IntConst 0)) 
                (mk_app (Ident PreambleConsts.frac_own_destr_ident) 
                  [(mk_select field_trsnl.field_heap term1)]
                )
              )
            with
            | Error.Msg (_loc, msg) -> Error.error (loc) (Printf.sprintf "%s: Checking field_read permission for '%s' failed." msg (Expr.to_string expr))
            
            in

          mk_app (Ident PreambleConsts.frac_val_destr_ident) [(mk_app Select [(field_trsnl.field_heap); term1])], session

        | _ -> Error.error (Expr.loc expr) "Expected field for read_expr in smtEnv; found something else."
        )
      | _ -> Error.error (Expr.loc expr) "Invalid read_expr found"
      )

    | expr -> translate_expr expr tbl smtEnv, session
  
  )

and trnsl_inhale (expr: expr) (tbl: SymbolTbl.t) (smtEnv: smt_env) : (qual_ident * SMTIdent.t) list * command list =
  match expr with
  | App (Own, [loc_expr; (App (Var field_heap, [], _)); val_expr; frac_expr], _) ->
    (match SmtEnv.find smtEnv field_heap with
    | Some (Field field_trnsl) ->
      let loc_term = translate_expr loc_expr tbl smtEnv in
      let val_term = translate_expr val_expr tbl smtEnv in
      let frac_term = translate_expr frac_expr tbl smtEnv in

      let old_fieldheap_term = field_trnsl.field_heap in
      let old_fieldheap = smt_ident_of_term old_fieldheap_term in
      let new_fieldheap = SMTIdent.fresh old_fieldheap.ident_name in
      let new_fieldheap_term = mk_const (Ident new_fieldheap) in
      
      let l_ident = SMTIdent.make "l" in
      let l_term = mk_const (Ident l_ident) in
      let cmd = 
        mk_assert (mk_binder Forall [(l_ident, PreambleConsts.loc_sort)] 
          (mk_ite (mk_eq l_term loc_term)
            (mk_eq (mk_select new_fieldheap_term l_term) (mk_app (Ident field_trnsl.field_heap_add_chunk) [mk_select old_fieldheap_term l_term; frac_chunk_constr val_term frac_term]))
            (mk_eq (mk_select new_fieldheap_term l_term) (mk_select old_fieldheap_term l_term))
          )
        ) in

        [(field_heap, new_fieldheap)], [cmd]
        
    | _ -> Error.error (Expr.loc expr) "Field not found in smtEnv")

  | App (Call, (App (Var pred_name, [], _)) :: args_list, _) ->
    (match SmtEnv.find smtEnv pred_name with
    | Some (Pred pred_trnsl) ->
      (let old_predheap_term = pred_trnsl.pred_heap in
      let old_predheap = smt_ident_of_term old_predheap_term in
      let new_predheap = SMTIdent.fresh old_predheap.ident_name in
      let new_predheap_term = mk_const (Ident new_predheap) in

      let args_terms = List.map args_list ~f:(fun expr -> translate_expr expr tbl smtEnv) in

      let pred_decl = pred_trnsl.pred_def.func_decl in

      let new_params_sort_list = List.filter_mapi pred_decl.call_decl_formals ~f:(fun index ident -> 
        let var_decl = Map.find_exn pred_decl.call_decl_locals ident in
        (* TODO: Make sure ghost/implicit is being treated properly *)
        if not var_decl.var_implicit then
          let tp = var_decl.var_type in
          let sort = lookup_type tp tbl smtEnv in
          Some (SMTIdent.fresh ("x" ^ Int.to_string index), sort)
        else
          None
        )
      in

      let new_params_list = List.map new_params_sort_list ~f:fst in

      let new_params_term_list = List.map new_params_list ~f:(fun ident -> mk_const (Ident ident)) in

      (* remove expr given for implicit args *)
      let arg_terms_truncated, _ = List.split_n args_terms (List.length new_params_list) in 

      let new_params_eq_old_expr_list = List.map2_exn new_params_list arg_terms_truncated ~f:(fun iden arg_term -> mk_eq (mk_const (Ident iden)) arg_term) in

      let cmd = 
        mk_assert (mk_binder Forall new_params_sort_list
          (mk_ite (mk_and new_params_eq_old_expr_list)
            (mk_eq 
              (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list)) 
              (mk_app Plus [mk_const (IntConst 1); (mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list))])
            )
            (mk_eq 
              (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list)) 
              (mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list))
            )
          )
        ) in 
      
      [(pred_name, new_predheap)], [cmd]
      )

    | Some (Func _func_trnsl) -> 
      let term = try
        translate_expr expr tbl smtEnv
      with
        Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in inhale: %s" (Expr.to_string expr) )
      in

      let cmd = mk_assert term in

      [], [cmd]

    | _ -> Error.error (Expr.loc expr) "Pred not found in smtEnv")

  | App (And, [expr1; expr2], _) -> 
    let new_vars, cmds = trnsl_inhale expr1 tbl smtEnv in
    
    let smtEnv' = update_env smtEnv new_vars in

    let new_vars', cmds' = trnsl_inhale expr2 tbl smtEnv' in

    new_vars @ new_vars', cmds @ cmds'

  | App (Ite, [expr0; expr1; expr2], _) ->
    (let new_vars1, cmds1 = trnsl_inhale expr1 tbl smtEnv in
    let new_vars2, cmds2 = trnsl_inhale expr2 tbl smtEnv in

    let new_vars3 = new_vars_unify new_vars1 new_vars2 in

    let smtEnv1 = update_env smtEnv new_vars1 in
    let smtEnv2 = update_env smtEnv new_vars2 in

    let new_var_eqs1 = List.map new_vars3 ~f:(fun (qual_ident, smt_ident) ->
      let old_term = SmtEnv.find_term_exn smtEnv1 qual_ident

      in
      mk_eq (mk_const (Ident smt_ident)) old_term

    ) in

    let new_var_eqs2 = List.map new_vars3 ~f:(fun (qual_ident, smt_ident) ->
      let old_term = SmtEnv.find_term_exn smtEnv2 qual_ident

      in
      mk_eq (mk_const (Ident smt_ident)) old_term

    ) in

    let cond_term = translate_expr expr0 tbl smtEnv in
    
    let cmd = mk_assert (mk_ite cond_term
      (mk_and (List.map cmds1 ~f:unfold_assert @ new_var_eqs1))
      (mk_and (List.map cmds2 ~f:unfold_assert @ new_var_eqs2))
    )
  
    in

    new_vars1 @ new_vars2 @ new_vars3, cmds1 @ cmds2 @ [cmd])

  | Binder (Forall, quant_vars, App (Own, [loc_expr; (App (Var field_heap, [], expr_attr0)); val_expr; frac_expr], expr_attr1), expr_attr2) ->

    trnsl_inhale
    (Binder (Forall, quant_vars, 
      App (Impl, [Expr.mk_bool true ; 
        App (Own, [loc_expr; (App (Var field_heap, [], expr_attr0)); val_expr; frac_expr], expr_attr1)
      ], expr_attr1
      ), expr_attr2
    )) tbl smtEnv


  | Binder (Forall, quant_vars, 
      App (Impl, [expr0; 
        App (Own, [loc_expr; (App (Var field_heap, [], _)); val_expr; frac_expr], _)], _
      ), _
    ) -> 
      (match SmtEnv.find smtEnv field_heap with
      | Some (Field field_trnsl) ->
        let old_fieldheap_term = field_trnsl.field_heap in
        let old_fieldheap = smt_ident_of_term old_fieldheap_term in
        let new_fieldheap = SMTIdent.fresh old_fieldheap.ident_name in
        let new_fieldheap_term = mk_const (Ident new_fieldheap) in
        
        let quant_var_sort_list = List.map quant_vars ~f:(fun var_decl -> 
          let tp = var_decl.var_type in
          let sort = lookup_type tp tbl smtEnv in

          (SMTIdent.fresh (Ident.to_string var_decl.var_name), sort)
          )
        in

        let smtEnv' = SmtEnv.push smtEnv in
        let smtEnv' = List.fold (List.zip_exn (List.map quant_vars ~f:(fun var -> QualIdent.from_ident (var.var_name))) quant_var_sort_list) ~init:smtEnv' ~f:(fun smtEnv (qual_ident, (smt_ident, sort)) -> SmtEnv.add smtEnv qual_ident (Var {var_symbol = mk_const (Ident smt_ident); var_sort = sort})) in

        let cond_term = translate_expr expr0 tbl smtEnv' in
        let loc_term = translate_expr loc_expr tbl smtEnv' in
        let val_term = translate_expr val_expr tbl smtEnv' in
        let frac_term = translate_expr frac_expr tbl smtEnv' in

        let l_ident = SMTIdent.make "l" in
        let l_term = mk_const (Ident l_ident) in

        let cmd1 = 
          mk_assert (mk_forall quant_var_sort_list 
            (mk_impl cond_term
              (mk_eq 
                (mk_select new_fieldheap_term loc_term)
                (mk_app (Ident field_trnsl.field_heap_add_chunk) [mk_select old_fieldheap_term loc_term; frac_chunk_constr val_term frac_term])
              )
            )
          ) in

        let cmd2 = 
          mk_assert (mk_forall [(l_ident, PreambleConsts.loc_sort)]
            (mk_or [
              mk_exists quant_var_sort_list (mk_and [mk_eq l_term loc_term; cond_term]);
              mk_eq (mk_select new_fieldheap_term l_term) (mk_select old_fieldheap_term l_term)
            ])
          ) in

          [(field_heap, new_fieldheap)], [cmd1; cmd2]
          
      | _ -> Error.error (Expr.loc expr) "Field not found in smtEnv"
      )

  | Binder (Forall, quant_vars, App (Call, (App (Var pred_name, [], expr_attr0)) :: args_list, expr_attr1), expr_attr2) ->
    trnsl_inhale
    (Binder (Forall, quant_vars, 
      App (Impl, [Expr.mk_bool true ; 
        App (Call, (App (Var pred_name, [], expr_attr0)) :: args_list, expr_attr1)
      ], expr_attr1
      ), expr_attr2
    )) tbl smtEnv

  | Binder (Forall, quant_vars, 
      App (Impl, [expr0; 
        App (Call, (App (Var pred_name, [], _)) :: args_list, _)
      ], _
      ), _
    ) ->
      (match SmtEnv.find smtEnv pred_name with
      | Some (Pred pred_trnsl) ->
        let old_predheap_term = pred_trnsl.pred_heap in
        let old_predheap = smt_ident_of_term old_predheap_term in
        let new_predheap = SMTIdent.fresh old_predheap.ident_name in
        let new_predheap_term = mk_const (Ident new_predheap) in
        
        let quant_var_sort_list = List.map quant_vars ~f:(fun var_decl -> 
          let tp = var_decl.var_type in
          let sort = lookup_type tp tbl smtEnv in

          (SMTIdent.fresh (Ident.to_string var_decl.var_name), sort)
          )
        in

        let quant_var_list = List.map quant_var_sort_list ~f:fst in

        let _quant_var_term_list = List.map quant_var_list ~f:(fun ident -> mk_const (Ident ident)) in

        let smtEnv' = SmtEnv.push smtEnv in
        let smtEnv' = List.fold (List.zip_exn (List.map quant_vars ~f:(fun var -> QualIdent.from_ident (var.var_name))) quant_var_sort_list) ~init:smtEnv' ~f:(fun smtEnv (qual_ident, (smt_ident, sort)) -> SmtEnv.add smtEnv qual_ident (Var {var_symbol = mk_const (Ident smt_ident); var_sort = sort})) in

        let cond_term = translate_expr expr0 tbl smtEnv' in
        let args_terms = List.map args_list ~f:(fun expr -> translate_expr expr tbl smtEnv') in

        let pred_decl = pred_trnsl.pred_def.func_decl in

        let new_params_sort_list = List.filter_mapi pred_decl.call_decl_formals ~f:(fun index ident -> 
          let var_decl = Map.find_exn pred_decl.call_decl_locals ident in
          (* TODO: Make sure ghost/implicit is being treated properly *)
          if not var_decl.var_implicit then
            let tp = var_decl.var_type in
            let sort = lookup_type tp tbl smtEnv in
            Some (SMTIdent.fresh ("x" ^ Int.to_string index), sort)
          else
            None
          )
        in

        let new_params_list = List.map new_params_sort_list ~f:fst in

        let new_params_term_list = List.map new_params_list ~f:(fun ident -> mk_const (Ident ident)) in

        (* remove expr given for implicit args *)
        let arg_terms_truncated, _ = List.split_n args_terms (List.length new_params_list) in 

        let new_params_eq_old_expr_list = List.map2_exn new_params_list arg_terms_truncated ~f:(fun iden arg_term -> mk_eq (mk_const (Ident iden)) arg_term) in

        let cmd1 = 
          mk_assert (mk_forall quant_var_sort_list 
            (mk_impl cond_term
              (mk_eq 
                (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated))
                (mk_app Plus [mk_const (IntConst 1); mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated)])
              )
            )
          ) in

        let cmd2 = 
          mk_assert (mk_forall new_params_sort_list
            (mk_or [
              mk_exists quant_var_sort_list (mk_and (cond_term :: new_params_eq_old_expr_list));
              mk_eq (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list)) (mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list))
            ])
          ) in

          [(pred_name, new_predheap)], [cmd1; cmd2]
        
      | Some (Func _) ->
        let term = try
          translate_expr expr tbl smtEnv
        with
          Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in inhale: %s" (Expr.to_string expr) )
        in
  
        let cmd = mk_assert term in
  
        [], [cmd]
          
      | _ -> Error.error (Expr.loc expr) "Pred not found in smtEnv"
      )

  | Binder (Forall, _quant_vars, _expr', _) ->
    let term = try
      translate_expr expr tbl smtEnv
    with
      Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in inhale: %s" (Expr.to_string expr) )
    in

    let cmd = 
      mk_assert term in

    [], [cmd]
  
  | Binder (Exists, quant_vars, App (Own, [loc_expr; (App (Var field_heap, [], expr_attr0)); val_expr; frac_expr], expr_attr1), expr_attr2) ->

    trnsl_inhale
    (Binder (Exists, quant_vars, 
      App (Impl, [Expr.mk_bool true ; 
        App (Own, [loc_expr; (App (Var field_heap, [], expr_attr0)); val_expr; frac_expr], expr_attr1)
      ], expr_attr1
      ), expr_attr2
    )) tbl smtEnv


  | Binder (Exists, quant_vars, 
      App (Impl, [expr0; 
        App (Own, [loc_expr; (App (Var field_heap, [], _)); val_expr; frac_expr], _)], _
      ), _
    ) -> 
      (match SmtEnv.find smtEnv field_heap with
      | Some (Field field_trnsl) ->
        let old_fieldheap_term = field_trnsl.field_heap in
        let old_fieldheap = smt_ident_of_term old_fieldheap_term in
        let new_fieldheap = SMTIdent.fresh old_fieldheap.ident_name in
        let new_fieldheap_term = mk_const (Ident new_fieldheap) in
        
        let quant_var_sort_list = List.map quant_vars ~f:(fun var_decl -> 
          let tp = var_decl.var_type in
          let sort = lookup_type tp tbl smtEnv in

          (SMTIdent.fresh (Ident.to_string var_decl.var_name), sort)
          )
        in

        let smtEnv' = SmtEnv.push smtEnv in
        let smtEnv' = List.fold (List.zip_exn (List.map quant_vars ~f:(fun var -> QualIdent.from_ident (var.var_name))) quant_var_sort_list) ~init:smtEnv' ~f:(fun smtEnv (qual_ident, (smt_ident, sort)) -> SmtEnv.add smtEnv qual_ident (Var {var_symbol = mk_const (Ident smt_ident); var_sort = sort})) in

        let cond_term = translate_expr expr0 tbl smtEnv' in
        let loc_term = translate_expr loc_expr tbl smtEnv' in
        let val_term = translate_expr val_expr tbl smtEnv' in
        let frac_term = translate_expr frac_expr tbl smtEnv' in

        let l_ident = SMTIdent.make "l" in
        let l_term = mk_const (Ident l_ident) in

        let cmd = 
          mk_assert (mk_exists quant_var_sort_list 
            (mk_impl cond_term
              (mk_and [
                (mk_eq 
                  (mk_select new_fieldheap_term loc_term)
                  (mk_app (Ident field_trnsl.field_heap_add_chunk) [mk_select old_fieldheap_term loc_term; frac_chunk_constr val_term frac_term])
                );

                (mk_forall [(l_ident, PreambleConsts.loc_sort)]
                  (mk_or [
                    mk_and [cond_term; mk_eq l_term loc_term];
                    mk_eq (mk_select new_fieldheap_term l_term) (mk_select old_fieldheap_term l_term)
                  ])
                )
              ])
            )
          ) in

          [(field_heap, new_fieldheap)], [cmd]
          
      | _ -> Error.error (Expr.loc expr) "Field not found in smtEnv"
      )

  | Binder (Exists, quant_vars, App (Call, (App (Var pred_name, [], expr_attr0)) :: args_list, expr_attr1), expr_attr2) ->
    trnsl_inhale
    (Binder (Exists, quant_vars, 
      App (Impl, [Expr.mk_bool true ; 
        App (Call, (App (Var pred_name, [], expr_attr0)) :: args_list, expr_attr1)
      ], expr_attr1
      ), expr_attr2
    )) tbl smtEnv

  | Binder (Exists, quant_vars, 
      App (Impl, [expr0; 
        App (Call, (App (Var pred_name, [], _)) :: args_list, _)
      ], _
      ), _
    ) ->
      (match SmtEnv.find smtEnv pred_name with
      | Some (Pred pred_trnsl) ->
        let old_predheap_term = pred_trnsl.pred_heap in
        let old_predheap = smt_ident_of_term old_predheap_term in
        let new_predheap = SMTIdent.fresh old_predheap.ident_name in
        let new_predheap_term = mk_const (Ident new_predheap) in
        
        let quant_var_sort_list = List.map quant_vars ~f:(fun var_decl -> 
          let tp = var_decl.var_type in
          let sort = lookup_type tp tbl smtEnv in

          (SMTIdent.fresh (Ident.to_string var_decl.var_name), sort)
          )
        in

        let quant_var_list = List.map quant_var_sort_list ~f:fst in

        let _quant_var_term_list = List.map quant_var_list ~f:(fun ident -> mk_const (Ident ident)) in      

        let smtEnv' = SmtEnv.push smtEnv in
        let smtEnv' = List.fold (List.zip_exn (List.map quant_vars ~f:(fun var -> QualIdent.from_ident (var.var_name))) quant_var_sort_list) ~init:smtEnv' ~f:(fun smtEnv (qual_ident, (smt_ident, sort)) -> SmtEnv.add smtEnv qual_ident (Var {var_symbol = mk_const (Ident smt_ident); var_sort = sort})) in

        let cond_term = translate_expr expr0 tbl smtEnv' in
        let args_terms = List.map args_list ~f:(fun expr -> translate_expr expr tbl smtEnv') in

        let pred_decl = pred_trnsl.pred_def.func_decl in

        let new_params_sort_list = List.filter_mapi pred_decl.call_decl_formals ~f:(fun index ident -> 
          let var_decl = Map.find_exn pred_decl.call_decl_locals ident in
          (* TODO: Make sure ghost/implicit is being treated properly *)
          if not var_decl.var_implicit then
            let tp = var_decl.var_type in
            let sort = lookup_type tp tbl smtEnv in
            Some (SMTIdent.fresh ("x" ^ Int.to_string index), sort)
          else
            None
          )
        in

        let new_params_list = List.map new_params_sort_list ~f:fst in

        let _new_params_term_list = List.map new_params_list ~f:(fun ident -> mk_const (Ident ident)) in

        (* remove expr given for implicit args *)
        let arg_terms_truncated, _ = List.split_n args_terms (List.length new_params_list) in 

        let new_params_eq_old_expr_list = List.map2_exn new_params_list arg_terms_truncated ~f:(fun iden arg_term -> mk_eq (mk_const (Ident iden)) arg_term) in

        let cmd = 
          mk_assert (mk_exists quant_var_sort_list 
            (mk_impl cond_term
              (mk_and [
                (mk_eq 
                  (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated))
                  (mk_app Plus [mk_const (IntConst 1); mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated)])
                );

                mk_forall new_params_sort_list
                (mk_or [
                  mk_and (cond_term :: new_params_eq_old_expr_list);

                  (mk_eq 
                    (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated))
                    (mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated))
                  ) 
                ])
              ])
            )
          ) in

          [(pred_name, new_predheap)], [cmd]

      | Some (Func _) ->
        let term = try
          translate_expr expr tbl smtEnv
        with
          Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in inhale: %s" (Expr.to_string expr) )
        in
  
        let cmd = mk_assert term in
  
        [], [cmd]
          
      | _ -> Error.error (Expr.loc expr) "Pred not found in smtEnv"
      )

  | Binder (Exists, _quant_vars, _expr, _) ->
    let term = try
      translate_expr expr tbl smtEnv
    with
      Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in inhale: %s" (Expr.to_string expr) )
    in

    let cmd = 
      mk_assert term in

    [], [cmd]

  | expr -> 
    let expr_term = try
      translate_expr expr tbl smtEnv
    with
      Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in inhale: %s" (Expr.to_string expr) )
    in

    let cmd = mk_assert expr_term in

    [], [cmd]




(* ------------------------------------------ *)






and trnsl_exhale (expr: expr) (tbl: SymbolTbl.t) (smtEnv: smt_env) : (qual_ident * SMTIdent.t) list * command list * term list =
  match expr with
  | App (Own, [loc_expr; (App (Var field_heap, [], _)); val_expr; frac_expr], _) ->
    (match SmtEnv.find smtEnv field_heap with
    | Some (Field field_trnsl) ->
      let loc_term = translate_expr loc_expr tbl smtEnv in
      let val_term = translate_expr val_expr tbl smtEnv in
      let frac_term = translate_expr frac_expr tbl smtEnv in

      let old_fieldheap_term = field_trnsl.field_heap in
      let old_fieldheap = smt_ident_of_term old_fieldheap_term in
      let new_fieldheap = SMTIdent.fresh old_fieldheap.ident_name in
      let new_fieldheap_term = mk_const (Ident new_fieldheap) in
      
      let l_ident = SMTIdent.make "l" in
      let l_term = mk_const (Ident l_ident) in
      let cmd = 
        mk_assert (mk_binder Forall [(l_ident, PreambleConsts.loc_sort)] 
          (mk_ite (mk_eq l_term loc_term)
            (mk_eq (mk_select new_fieldheap_term l_term) (mk_app (Ident field_trnsl.field_heap_subtract_chunk) [mk_select old_fieldheap_term l_term;  frac_chunk_constr val_term frac_term]))
            (mk_eq (mk_select new_fieldheap_term l_term) (mk_select old_fieldheap_term l_term))
          )
        ) in
      
      let permission_term =
        mk_app (Ident field_trnsl.heapchunk_compare) [
          frac_chunk_constr val_term frac_term;
          (mk_select old_fieldheap_term loc_term)
        ] in

      [(field_heap, new_fieldheap)], [cmd], [permission_term]
        
    | _ -> Error.error (Expr.loc expr) "Field not found in smtEnv")

  | App (Call, (App (Var call_name, [], _)) :: args_list, _) ->
    (match SmtEnv.find smtEnv call_name with
    | Some (Pred pred_trnsl) ->
      (let old_predheap_term = pred_trnsl.pred_heap in
      let old_predheap = smt_ident_of_term old_predheap_term in
      let new_predheap = SMTIdent.fresh old_predheap.ident_name in
      let new_predheap_term = mk_const (Ident new_predheap) in

      let args_terms = List.map args_list ~f:(fun expr -> translate_expr expr tbl smtEnv) in

      let pred_decl = pred_trnsl.pred_def.func_decl in

      let new_params_sort_list = List.filter_mapi pred_decl.call_decl_formals ~f:(fun index ident -> 
        let var_decl = Map.find_exn pred_decl.call_decl_locals ident in
        (* TODO: Make sure ghost/implicit is being treated properly *)
        if not var_decl.var_implicit then
          let tp = var_decl.var_type in
          let sort = lookup_type tp tbl smtEnv in
          Some (SMTIdent.fresh ("x" ^ Int.to_string index), sort)
        else
          None
        )
      in

      let new_params_list = List.map new_params_sort_list ~f:fst in

      let new_params_term_list = List.map new_params_list ~f:(fun ident -> mk_const (Ident ident)) in

      (* remove expr given for implicit args *)
      let arg_terms_truncated, _ = List.split_n args_terms (List.length new_params_list) in 

      let new_params_eq_old_expr_list = List.map2_exn new_params_list arg_terms_truncated ~f:(fun iden arg_term -> mk_eq (mk_const (Ident iden)) arg_term) in

      let cmd = 
        mk_assert (mk_binder Forall new_params_sort_list
          (mk_ite (mk_and new_params_eq_old_expr_list)
            (mk_eq 
              (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list)) 
              (mk_app Minus [(mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list)); mk_const (IntConst 1)])
            )
            (mk_eq 
              (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list)) 
              (mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list))
            )
          )
        ) in

      let permission_term = 
        mk_leq (mk_const (IntConst 1)) (mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated))

      in
      
      [(call_name, new_predheap)], [cmd], [permission_term]
      )
    
    | Some (Func _func_trnsl) -> 
      let term = try
          translate_expr expr tbl smtEnv
        with
        Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in exhale: %s" (Expr.to_string expr) )
      in
      [], [], [term]

    | _ -> Error.error (Expr.loc expr) @@ Printf.sprintf "Callable %s not found in smtEnv. \nsmtEnv: %s " (QualIdent.to_string call_name) (SmtEnv.to_string smtEnv))

  | App (And, [expr1; expr2], _) -> 
    let new_vars, cmds, perm_terms = trnsl_exhale expr1 tbl smtEnv in
    
    let smtEnv' = update_env smtEnv new_vars in

    let new_vars', cmds', perm_terms' = trnsl_exhale expr2 tbl smtEnv' in

    new_vars @ new_vars', cmds @ cmds', perm_terms @ perm_terms'

  | App (Ite, [expr0; expr1; expr2], _) ->
    (let new_vars1, cmds1, perm_terms1 = trnsl_exhale expr1 tbl smtEnv in
    let new_vars2, cmds2, perm_terms2 = trnsl_exhale expr2 tbl smtEnv in

    let new_vars3 = new_vars_unify new_vars1 new_vars2 in

    let smtEnv1 = update_env smtEnv new_vars1 in
    let smtEnv2 = update_env smtEnv new_vars2 in

    let new_var_eqs1 = List.map new_vars3 ~f:(fun (qual_ident, smt_ident) ->
      let old_term = (match SmtEnv.find smtEnv1 qual_ident with
      | Some (Pred pred_trnsl) -> pred_trnsl.pred_heap
      | Some (Field field_trnsl) -> field_trnsl.field_heap
      | _ -> Error.error (Expr.loc expr1) "Expected field or predicate when updating env vars; found something else.")

      in
      mk_eq (mk_const (Ident smt_ident)) old_term

    ) in

    let new_var_eqs2 = List.map new_vars3 ~f:(fun (qual_ident, smt_ident) ->
      let old_term = (match SmtEnv.find smtEnv2 qual_ident with
      | Some (Pred pred_trnsl) -> pred_trnsl.pred_heap
      | Some (Field field_trnsl) -> field_trnsl.field_heap
      | _ -> Error.error (Expr.loc expr1) "Expected field or predicate when updating env vars; found something else.")

      in
      mk_eq (mk_const (Ident smt_ident)) old_term

    ) in

    let cond_term = translate_expr expr0 tbl smtEnv in
    
    let cmd = mk_assert (mk_ite cond_term
      (mk_and (List.map cmds1 ~f:unfold_assert @ new_var_eqs1))
      (mk_and (List.map cmds2 ~f:unfold_assert @ new_var_eqs2))
    )
  
    in

    let perm_terms1 = List.map perm_terms1 ~f:(fun term -> mk_impl cond_term term) in

    let perm_terms2 = List.map perm_terms2 ~f:(fun term -> mk_impl (mk_not cond_term) term) in

    new_vars1 @ new_vars2 @ new_vars3, cmds1 @ cmds2 @ [cmd], perm_terms1 @ perm_terms2)

  | Binder (Forall, quant_vars, App (Own, [loc_expr; (App (Var field_heap, [], expr_attr0)); val_expr; frac_expr], expr_attr1), expr_attr2) ->
    trnsl_exhale
    (Binder (Forall, quant_vars, 
      App (Impl, [Expr.mk_bool true ; 
        App (Own, [loc_expr; (App (Var field_heap, [], expr_attr0)); val_expr; frac_expr], expr_attr1)
      ], expr_attr1
      ), expr_attr2
    )) tbl smtEnv


  | Binder (Forall, quant_vars, 
      App (Impl, [expr0; 
        App (Own, [loc_expr; (App (Var field_heap, [], _)); val_expr; frac_expr], _)], _
      ), _
    ) -> 
      (match SmtEnv.find smtEnv field_heap with
      | Some (Field field_trnsl) ->
        let old_fieldheap_term = field_trnsl.field_heap in
        let old_fieldheap = smt_ident_of_term old_fieldheap_term in
        let new_fieldheap = SMTIdent.fresh old_fieldheap.ident_name in
        let new_fieldheap_term = mk_const (Ident new_fieldheap) in
        
        let quant_var_sort_list = List.map quant_vars ~f:(fun var_decl -> 
          let tp = var_decl.var_type in
          let sort = lookup_type tp tbl smtEnv in

          (SMTIdent.fresh (Ident.to_string var_decl.var_name), sort)
          )
        in

        let smtEnv' = SmtEnv.push smtEnv in
        let smtEnv' = List.fold (List.zip_exn (List.map quant_vars ~f:(fun var -> QualIdent.from_ident (var.var_name))) quant_var_sort_list) ~init:smtEnv' ~f:(fun smtEnv (qual_ident, (smt_ident, sort)) -> SmtEnv.add smtEnv qual_ident (Var {var_symbol = mk_const (Ident smt_ident); var_sort = sort})) in

        let cond_term = translate_expr expr0 tbl smtEnv' in
        let loc_term = translate_expr loc_expr tbl smtEnv' in
        let val_term = translate_expr val_expr tbl smtEnv' in
        let frac_term = translate_expr frac_expr tbl smtEnv' in

        let l_ident = SMTIdent.make "l" in
        let l_term = mk_const (Ident l_ident) in

        let cmd1 = 
          mk_assert (mk_forall quant_var_sort_list 
            (mk_impl cond_term
              (mk_eq 
                (mk_select new_fieldheap_term loc_term)
                (mk_app (Ident field_trnsl.field_heap_subtract_chunk) [mk_select old_fieldheap_term loc_term; frac_chunk_constr val_term frac_term])
              )
            )
          ) in

        let cmd2 = 
          mk_assert (mk_forall [(l_ident, PreambleConsts.loc_sort)]
            (mk_or [
              mk_exists quant_var_sort_list (mk_and [mk_eq l_term loc_term; cond_term]);
              mk_eq (mk_select new_fieldheap_term l_term) (mk_select old_fieldheap_term l_term)
            ])
          ) in

          let perm_term = (
            mk_forall quant_var_sort_list 
            (mk_impl cond_term
              (mk_app (Ident field_trnsl.heapchunk_compare) [
                frac_chunk_constr val_term frac_term;
                (mk_select old_fieldheap_term loc_term);
              ])
            )
          ) in

          [(field_heap, new_fieldheap)], [cmd1; cmd2], [perm_term]
          
      | _ -> Error.error (Expr.loc expr) "Field not found in smtEnv"
      )

  | Binder (Forall, quant_vars, App (Call, (App (Var pred_name, [], expr_attr0)) :: args_list, expr_attr1), expr_attr2) ->
    trnsl_exhale
    (Binder (Forall, quant_vars, 
      App (Impl, [Expr.mk_bool true ; 
        App (Call, (App (Var pred_name, [], expr_attr0)) :: args_list, expr_attr1)
      ], expr_attr1
      ), expr_attr2
    )) tbl smtEnv

  | Binder (Forall, quant_vars, 
      App (Impl, [expr0; 
        App (Call, (App (Var pred_name, [], _)) :: args_list, _)
      ], _
      ), _
    ) ->
      (match SmtEnv.find smtEnv pred_name with
      | Some (Pred pred_trnsl) ->
        let old_predheap_term = pred_trnsl.pred_heap in
        let old_predheap = smt_ident_of_term old_predheap_term in
        let new_predheap = SMTIdent.fresh old_predheap.ident_name in
        let new_predheap_term = mk_const (Ident new_predheap) in
        
        let quant_var_sort_list = List.map quant_vars ~f:(fun var_decl -> 
          let tp = var_decl.var_type in
          let sort = lookup_type tp tbl smtEnv in

          (SMTIdent.fresh (Ident.to_string var_decl.var_name), sort)
          )
        in

        let quant_var_list = List.map quant_var_sort_list ~f:fst in

        let _quant_var_term_list = List.map quant_var_list ~f:(fun ident -> mk_const (Ident ident)) in      

        let smtEnv' = SmtEnv.push smtEnv in
        let smtEnv' = List.fold (List.zip_exn (List.map quant_vars ~f:(fun var -> QualIdent.from_ident (var.var_name))) quant_var_sort_list) ~init:smtEnv' ~f:(fun smtEnv (qual_ident, (smt_ident, sort)) -> SmtEnv.add smtEnv qual_ident (Var {var_symbol = mk_const (Ident smt_ident); var_sort = sort})) in

        let cond_term = translate_expr expr0 tbl smtEnv' in
        let args_terms = List.map args_list ~f:(fun expr -> translate_expr expr tbl smtEnv') in

        let pred_decl = pred_trnsl.pred_def.func_decl in

        let new_params_sort_list = List.filter_mapi pred_decl.call_decl_formals ~f:(fun index ident -> 
          let var_decl = Map.find_exn pred_decl.call_decl_locals ident in
          (* TODO: Make sure ghost/implicit is being treated properly *)
          if not var_decl.var_implicit then
            let tp = var_decl.var_type in
            let sort = lookup_type tp tbl smtEnv in
            Some (SMTIdent.fresh ("x" ^ Int.to_string index), sort)
          else
            None
          )
        in

        let new_params_list = List.map new_params_sort_list ~f:fst in

        let new_params_term_list = List.map new_params_list ~f:(fun ident -> mk_const (Ident ident)) in

        (* remove expr given for implicit args *)
        let arg_terms_truncated, _ = List.split_n args_terms (List.length new_params_list) in 

        let new_params_eq_old_expr_list = List.map2_exn new_params_list arg_terms_truncated ~f:(fun iden arg_term -> mk_eq (mk_const (Ident iden)) arg_term) in

        let cmd1 = 
          mk_assert (mk_forall quant_var_sort_list 
            (mk_impl cond_term
              (mk_eq 
                (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated))
                (mk_app Minus [mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated); mk_const (IntConst 1);])
              )
            )
          ) in

        let cmd2 = 
          mk_assert (mk_forall new_params_sort_list
            (mk_or [
              mk_exists quant_var_sort_list (mk_and (cond_term :: new_params_eq_old_expr_list));

              mk_eq (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list)) (mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list))
            ])
          ) in

        let perm_term = (
          mk_forall quant_var_sort_list
          (mk_forall new_params_sort_list 
            (mk_impl cond_term
              (mk_leq 
                (mk_const (IntConst 1))
                (mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) new_params_term_list))
              )
            ))
        ) in

          [(pred_name, new_predheap)], [cmd1; cmd2], [perm_term]

      | Some (Func _) ->
        let term = try
          translate_expr expr tbl smtEnv
        with
          Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in exhale: %s" (Expr.to_string expr) )
    
        in
    
        [], [], [term]
          
      | _ -> Error.error (Expr.loc expr) @@ Printf.sprintf "Pred %s not found in smtEnv" (QualIdent.to_string pred_name)
      )

  | Binder (Forall, _quant_vars, _expr, _) ->
    let term = try
        translate_expr expr tbl smtEnv
      with
      Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in exhale: %s" (Expr.to_string expr) )
    in

    [], [], [term]
  
  | Binder (Exists, quant_vars, 
      App (Impl, [expr0; 
        App (Own, [loc_expr; (App (Var field_heap, [], _)); val_expr; frac_expr], _)], _
      ), _
    ) -> 
    (match SmtEnv.find smtEnv field_heap with
    | Some (Field field_trnsl) ->
      let old_fieldheap_term = field_trnsl.field_heap in
      let old_fieldheap = smt_ident_of_term old_fieldheap_term in
      let new_fieldheap = SMTIdent.fresh old_fieldheap.ident_name in
      let new_fieldheap_term = mk_const (Ident new_fieldheap) in
      
      let quant_var_sort_list = List.map quant_vars ~f:(fun var_decl -> 
        let tp = var_decl.var_type in
        let sort = lookup_type tp tbl smtEnv in

        (SMTIdent.fresh (Ident.to_string var_decl.var_name), sort)
        )
      in

      let smtEnv' = SmtEnv.push smtEnv in
      let smtEnv' = List.fold (List.zip_exn (List.map quant_vars ~f:(fun var -> QualIdent.from_ident (var.var_name))) quant_var_sort_list) ~init:smtEnv' ~f:(fun smtEnv (qual_ident, (smt_ident, sort)) -> SmtEnv.add smtEnv qual_ident (Var {var_symbol = mk_const (Ident smt_ident); var_sort = sort})) in

      let cond_term = translate_expr expr0 tbl smtEnv' in
      let loc_term = translate_expr loc_expr tbl smtEnv' in
      let val_term = translate_expr val_expr tbl smtEnv' in
      let frac_term = translate_expr frac_expr tbl smtEnv' in

      let l_ident = SMTIdent.make "l" in
      let l_term = mk_const (Ident l_ident) in

      let cmd = 
        mk_assert (mk_exists quant_var_sort_list 
          (mk_impl cond_term
            (mk_and [
              (mk_eq 
                (mk_select new_fieldheap_term loc_term)
                (mk_app (Ident field_trnsl.field_heap_subtract_chunk) [mk_select old_fieldheap_term loc_term; frac_chunk_constr val_term frac_term])
              );

              (mk_forall [(l_ident, PreambleConsts.loc_sort)]
                (mk_or [
                  mk_and [cond_term; mk_eq l_term loc_term];
                  mk_eq (mk_select new_fieldheap_term l_term) (mk_select old_fieldheap_term l_term)
                ])
              )
            ])
          )
        ) in

        let perm_term = 
          mk_exists quant_var_sort_list (mk_impl cond_term
            (mk_app (Ident field_trnsl.heapchunk_compare) [frac_chunk_constr val_term frac_term; mk_select old_fieldheap_term loc_term])
          ) in

        [(field_heap, new_fieldheap)], [cmd], [perm_term]
        
    | _ -> Error.error (Expr.loc expr) "Field not found in smtEnv"
    )

  | Binder (Exists, quant_vars, App (Call, (App (Var pred_name, [], expr_attr0)) :: args_list, expr_attr1), expr_attr2) ->
    trnsl_exhale
    (Binder (Exists, quant_vars, 
      App (Impl, [Expr.mk_bool true ; 
        App (Call, (App (Var pred_name, [], expr_attr0)) :: args_list, expr_attr1)
      ], expr_attr1
      ), expr_attr2
    )) tbl smtEnv

  | Binder (Exists, quant_vars, 
      App (Impl, [expr0; 
        App (Call, (App (Var pred_name, [], _)) :: args_list, _)
      ], _
      ), _
    ) ->
      (match SmtEnv.find smtEnv pred_name with
      | Some (Pred pred_trnsl) ->
        let old_predheap_term = pred_trnsl.pred_heap in
        let old_predheap = smt_ident_of_term old_predheap_term in
        let new_predheap = SMTIdent.fresh old_predheap.ident_name in
        let new_predheap_term = mk_const (Ident new_predheap) in
        
        let quant_var_sort_list = List.map quant_vars ~f:(fun var_decl -> 
          let tp = var_decl.var_type in
          let sort = lookup_type tp tbl smtEnv in

          (SMTIdent.fresh (Ident.to_string var_decl.var_name), sort)
          )
        in

        let quant_var_list = List.map quant_var_sort_list ~f:fst in

        let _quant_var_term_list = List.map quant_var_list ~f:(fun ident -> mk_const (Ident ident)) in      

        let smtEnv' = SmtEnv.push smtEnv in
        let smtEnv' = List.fold (List.zip_exn (List.map quant_vars ~f:(fun var -> QualIdent.from_ident (var.var_name))) quant_var_sort_list) ~init:smtEnv' ~f:(fun smtEnv (qual_ident, (smt_ident, sort)) -> SmtEnv.add smtEnv qual_ident (Var {var_symbol = mk_const (Ident smt_ident); var_sort = sort})) in

        let cond_term = translate_expr expr0 tbl smtEnv' in
        let args_terms = List.map args_list ~f:(fun expr -> translate_expr expr tbl smtEnv') in

        let pred_decl = pred_trnsl.pred_def.func_decl in

        let new_params_sort_list = List.filter_mapi pred_decl.call_decl_formals ~f:(fun index ident -> 
          let var_decl = Map.find_exn pred_decl.call_decl_locals ident in
          (* TODO: Make sure ghost/implicit is being treated properly *)
          if not var_decl.var_implicit then
            let tp = var_decl.var_type in
            let sort = lookup_type tp tbl smtEnv in
            Some (SMTIdent.fresh ("x" ^ Int.to_string index), sort)
          else
            None
          )
        in

        let new_params_list = List.map new_params_sort_list ~f:fst in

        let _new_params_term_list = List.map new_params_list ~f:(fun ident -> mk_const (Ident ident)) in

        (* remove expr given for implicit args *)
        let arg_terms_truncated, _ = List.split_n args_terms (List.length new_params_list) in 

        let new_params_eq_old_expr_list = List.map2_exn new_params_list arg_terms_truncated ~f:(fun iden arg_term -> mk_eq (mk_const (Ident iden)) arg_term) in

        let cmd = 
          mk_assert (mk_exists quant_var_sort_list 
            (mk_impl cond_term
              (mk_and [
                (mk_eq 
                  (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated))
                  (mk_app Minus [mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated); mk_const (IntConst 1)])
                );

                mk_forall new_params_sort_list
                (mk_or [
                  mk_and (cond_term :: new_params_eq_old_expr_list);

                  (mk_eq 
                    (mk_select new_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated))
                    (mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated))
                  ) 
                ])
              ])
            )
          ) in

          let perm_term = 
            mk_exists quant_var_sort_list (mk_impl cond_term
              (mk_leq 
                (mk_const (IntConst 1))
                (mk_select old_predheap_term (mk_app (Ident pred_trnsl.pred_constr) arg_terms_truncated))
              )
            )
          in

          [(pred_name, new_predheap)], [cmd], [perm_term]

      | Some (Func _) ->
        let term = try
          translate_expr expr tbl smtEnv
        with
          Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in exhale: %s" (Expr.to_string expr) )
    
        in
    
        [], [], [term]
          
      | _ -> Error.error (Expr.loc expr) "Pred not found in smtEnv"
      )

  | Binder (Exists, _quant_vars, _expr, _) ->
    let term = try
        translate_expr expr tbl smtEnv
      with
      Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in exhale: %s" (Expr.to_string expr) )
    in

    [], [], [term]

  | expr -> 
    let expr_term = try
      translate_expr expr tbl smtEnv
    with
      Error.Msg (loc, _msg) -> Error.error loc (Printf.sprintf "Unsupported expression found in exhale: %s" (Expr.to_string expr) )

    in

    [], [], [expr_term]



(* ------------- *)


let initialize_pred (func_def: Callable.func_def) ?(alias_name: QualIdent.t option) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: session) = 
  let func_decl = func_def.func_decl in
  let fully_qualified_name = 
    match alias_name with
    | None -> (SmtEnv.mk_qual_ident smtEnv func_decl.call_decl_name) 
    | Some qi -> (SmtEnv.mk_qual_ident_qi smtEnv (QualIdent.append qi func_decl.call_decl_name))
  in
  let pred_smt_ident = SMTIdent.make (QualIdent.to_string fully_qualified_name) in
  
  let arg_sort_list = (List.filter_map func_decl.call_decl_formals ~f:(fun iden -> 
    if (Map.find_exn func_decl.call_decl_locals iden).var_implicit then None else
          
    Some (SMTIdent.fresh (Ident.to_string iden),
    (lookup_type ((Map.find_exn func_decl.call_decl_locals iden).var_type) tbl smtEnv))
  ))

  in

  let sort_list = List.map arg_sort_list ~f:snd in

  let pred_sort_name = SMTIdent.fresh (pred_smt_ident.ident_name ^ "$Pred") in
  let pred_constr = SMTIdent.fresh (pred_sort_name.ident_name ^ "$Constr") in

  let args_destructors_sorts = List.mapi sort_list ~f:(fun index sort ->
    (SMTIdent.fresh (pred_sort_name.ident_name ^ "$Arg" ^ Int.to_string index), sort)
    ) in

  let pred_sort = AdtSort (pred_sort_name, [(pred_sort_name, [], [pred_constr, args_destructors_sorts])]) in

  Smt_solver.write session (mk_declare_datatype (pred_sort_name, [], [pred_constr, args_destructors_sorts]));

  let pred_heap_ident = SMTIdent.fresh (pred_sort_name.ident_name ^ "$Heap") in
  let pred_heap_term = mk_const (Ident pred_heap_ident) in

  Smt_solver.write session (mk_declare_const pred_heap_ident (mk_pred_heap_sort pred_sort));


  let index_ident = SMTIdent.make "$index" in

  let index_term = mk_const (Ident index_ident) in


  write session (mk_assert (mk_forall [index_ident, pred_sort]
    (mk_eq (mk_select (mk_const (Ident pred_heap_ident)) index_term) (mk_const (IntConst 0)))
  ));
  

  let (pred_trnsl: SmtEnv.pred_trnsl) = {
    pred_heap = pred_heap_term;
    pred_sort = pred_sort;
    pred_args = sort_list;
    pred_heap_sort = mk_pred_heap_sort pred_sort;
    pred_constr = pred_constr;
    pred_def = func_def;
  } in
  
  let smtEnv = SmtEnv.add smtEnv fully_qualified_name (Pred pred_trnsl) in

  smtEnv, session

let check_proc_def (proc_def: Callable.proc_def) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: session) =
  let proc_decl = proc_def.proc_decl in
  let fully_qualified_name = (SmtEnv.mk_qual_ident smtEnv proc_decl.call_decl_name) in
  let _proc_smt_ident = SMTIdent.make (QualIdent.to_string fully_qualified_name) in

  let arg_sort_list = (List.map proc_decl.call_decl_formals ~f:(fun iden -> 
    (SMTIdent.fresh (Ident.to_string iden),
    (lookup_type ((Map.find_exn proc_decl.call_decl_locals iden).var_type) tbl smtEnv))
    ))

  in

  let _sort_list = List.map arg_sort_list ~f:snd in

  let ret_args_sort_list = (List.map proc_decl.call_decl_returns ~f:(fun iden -> 
    (SMTIdent.fresh (Ident.to_string iden),
    (lookup_type ((Map.find_exn proc_decl.call_decl_locals iden).var_type) tbl smtEnv))
  )) in

  (match proc_def.proc_body with
  | None -> smtEnv, session
  | Some stmt ->
    let smtEnv = SmtEnv.push smtEnv in
    let session = Smt_solver.push session in

      let smtEnv = List.fold2_exn (proc_decl.call_decl_formals @ proc_decl.call_decl_returns) (arg_sort_list @ ret_args_sort_list) ~init:smtEnv ~f:(fun smtEnv' ident (smt_ident, sort) ->
        let (var_trnsl: SmtEnv.var_trnsl) = {
          var_symbol = mk_const (Ident smt_ident);
          var_sort = sort;
        }
        in

        SmtEnv.add smtEnv' (QualIdent.from_ident ident) (Var var_trnsl)
      ) in
      
      Smt_solver.write_comment session ("Initializing vars for proc_def " ^ (QualIdent.to_string fully_qualified_name));
      List.iter (arg_sort_list @ ret_args_sort_list) ~f:(fun (arg, sort) -> 
        Smt_solver.write session (mk_declare_const arg sort)
      );


      Smt_solver.write_comment session "Inhaling pre-conditions";
      let smtEnv, session = List.fold proc_decl.call_decl_precond ~init:(smtEnv, session) ~f:(fun (smtEnv, session) spec -> check_basic_stmt (Inhale spec.spec_form) [] tbl smtEnv session proc_decl.call_decl_loc) in

      Smt_solver.write_comment session "Executing body";
      let smtEnv, session = check_stmt stmt [] tbl smtEnv session in

      Smt_solver.write_comment session "Exhaling post-conditions";
      let smtEnv, session = List.fold proc_decl.call_decl_postcond ~init:(smtEnv, session) ~f:(fun (smtEnv, session) spec -> check_basic_stmt (Exhale spec.spec_form) [] tbl smtEnv session proc_decl.call_decl_loc) in

    
    let session = Smt_solver.pop session in
    let smtEnv = SmtEnv.pop smtEnv in
    
    smtEnv, session
  )


let check_interface_callable (callable: Callable.t) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: Smt_solver.session) : smt_env * Smt_solver.session = 
  match callable with
  | FuncDef func_def -> (
    let func_decl = func_def.func_decl in
    let fully_qualified_name = (SmtEnv.mk_qual_ident smtEnv func_decl.call_decl_name) in
    let func_smt_ident = SMTIdent.make (QualIdent.to_string fully_qualified_name) in

    (match func_decl.call_decl_kind with
    | Func -> (
      (* TODO: Make sure function's pre/post conditions are being verified here. *)

      let arg_sort_list = (List.map func_decl.call_decl_formals ~f:(fun iden -> 
        (SMTIdent.fresh (Ident.to_string iden),
        (lookup_type ((Map.find_exn func_decl.call_decl_locals iden).var_type) tbl smtEnv))
      ))

      in

      let sort_list = List.map arg_sort_list ~f:snd in

      let return_sort = (
        match func_decl.call_decl_returns with
        | [iden] -> 
          (lookup_type ((Map.find_exn func_decl.call_decl_locals iden).var_type) tbl smtEnv)

        | _ -> Error.unsupported_error (func_decl.call_decl_loc) "Only support functions which return one thing"
      ) in
        
      (match func_def.func_body with
      | None -> 
        Smt_solver.write session (mk_declare_fun func_smt_ident sort_list return_sort);

        let (func_trnsl: SmtEnv.func_trnsl) = {
          func_symbol = func_smt_ident;
          func_args = sort_list;
          func_return = return_sort;
        } in

        let smtEnv = SmtEnv.add smtEnv fully_qualified_name (Func func_trnsl) in

        smtEnv, session

      | Some expr ->
        let smtEnv = SmtEnv.push smtEnv in

          let smtEnv = List.fold2_exn func_decl.call_decl_formals arg_sort_list ~init:smtEnv ~f:(fun smtEnv ident (smt_ident, sort) ->
            let (var_trnsl: SmtEnv.var_trnsl) = {
              var_symbol = mk_const (Ident smt_ident);
              var_sort = sort;
            }
            in

            SmtEnv.add smtEnv (QualIdent.from_ident ident) (Var var_trnsl)
            )

          in

          let body_term = translate_expr expr tbl smtEnv in

          Smt_solver.write session (mk_define_fun func_smt_ident arg_sort_list return_sort body_term);
          

        let smtEnv = SmtEnv.pop smtEnv in

        let (func_trnsl: SmtEnv.func_trnsl) = {
          func_symbol = func_smt_ident;
          func_args = sort_list;
          func_return = return_sort;
        } in

        let smtEnv = SmtEnv.add smtEnv fully_qualified_name (Func func_trnsl) in

        smtEnv, session

      )

    )
    | Invariant
    | Pred -> 
      let smtEnv, session = initialize_pred func_def tbl smtEnv session in

      smtEnv, session
    | _ -> Error.error_simple "FuncDef can only be a func/invariant/pred, not proc/lemma"
    )
  )

  | ProcDef proc_def -> 
    let proc_decl = proc_def.proc_decl in
    let fully_qualified_name = (SmtEnv.mk_qual_ident smtEnv proc_decl.call_decl_name) in
    let _proc_smt_ident = SMTIdent.make (QualIdent.to_string fully_qualified_name) in

    let arg_sort_list = (List.map proc_decl.call_decl_formals ~f:(fun iden -> 
      (SMTIdent.fresh (Ident.to_string iden),
      (lookup_type ((Map.find_exn proc_decl.call_decl_locals iden).var_type) tbl smtEnv))
    ))

    in

    let _sort_list = List.map arg_sort_list ~f:snd in

    (match proc_decl.call_decl_kind with
     | Lemma (* ->
      (* Treating all lemmas in interfaces as axioms *)

      let smtEnv' = List.fold2_exn proc_decl.call_decl_formals arg_sort_list ~init:smtEnv ~f:(fun smtEnv' ident (smt_ident, sort) ->
        let (var_trnsl: SmtEnv.var_trnsl) = {
          var_symbol = mk_const (Ident smt_ident);
          var_sort = sort;
        }
        in

        SmtEnv.add smtEnv' (QualIdent.from_ident ident) (Var var_trnsl)
      )

      in

      let preconds = List.map proc_decl.call_decl_precond ~f:(fun spec -> translate_expr spec.spec_form tbl smtEnv') in

      let postconds = List.map proc_decl.call_decl_postcond ~f:(fun spec -> translate_expr spec.spec_form tbl smtEnv') in

      let precond_term = match preconds with
      | [] -> mk_const (BoolConst true)
      | [term] -> term
      | ts -> mk_and ts

      in

      let postcond_term = match postconds with
      | [] -> mk_const (BoolConst true)
      | [term] -> term
      | ts -> mk_and ts

      in

      Smt_solver.write session (mk_assert (mk_forall arg_sort_list
        (mk_impl precond_term postcond_term)
      ));

      smtEnv, session *)


    | Proc ->
      check_proc_def proc_def tbl smtEnv session

    | _ -> Error.error_simple "ProcDef can only be a proc/lemma, not func/invariant/pred."
    )

let check_module_callable (callable: Callable.t) ?(alias_name: QualIdent.t option) (tbl: SymbolTbl.t) (smtEnv: smt_env) (session: Smt_solver.session) : smt_env * Smt_solver.session =
  match callable with
  | FuncDef func_def -> (
    let func_decl = func_def.func_decl in
    let fully_qualified_name = 
      match alias_name with
      | None -> (SmtEnv.mk_qual_ident smtEnv func_decl.call_decl_name) 
      | Some qi -> (SmtEnv.mk_qual_ident_qi smtEnv (QualIdent.append qi func_decl.call_decl_name))
    in
    let func_smt_ident = SMTIdent.make (QualIdent.to_string fully_qualified_name) in

    (match func_decl.call_decl_kind with
    | Func -> (
      (* TODO: Make sure function's pre/post conditions are being verified here. *)

      let arg_sort_list = (List.map func_decl.call_decl_formals ~f:(fun iden -> 
        (SMTIdent.fresh (Ident.to_string iden),
        (lookup_type ((Map.find_exn func_decl.call_decl_locals iden).var_type) tbl smtEnv))
        ))

      in

      let sort_list = List.map arg_sort_list ~f:snd in

      let return_sort = (
        match func_decl.call_decl_returns with
        | [iden] -> 
          (lookup_type ((Map.find_exn func_decl.call_decl_locals iden).var_type) tbl smtEnv)

        | _ -> Error.unsupported_error (func_decl.call_decl_loc) "Only support functions which return one thing"
      ) in
        
      (match func_def.func_body with
      | None -> 
        Smt_solver.write session (mk_declare_fun func_smt_ident sort_list return_sort);

        let (func_trnsl: SmtEnv.func_trnsl) = {
          func_symbol = func_smt_ident;
          func_args = sort_list;
          func_return = return_sort;
        } in

        let smtEnv = SmtEnv.add smtEnv fully_qualified_name (Func func_trnsl) in

        smtEnv, session

      | Some expr ->
        let smtEnv = SmtEnv.push smtEnv in

          let smtEnv = List.fold2_exn func_decl.call_decl_formals arg_sort_list ~init:smtEnv ~f:(fun smtEnv ident (smt_ident, sort) ->
            let (var_trnsl: SmtEnv.var_trnsl) = {
              var_symbol = mk_const (Ident smt_ident);
              var_sort = sort;
            }
            in

            SmtEnv.add smtEnv (QualIdent.from_ident ident) (Var var_trnsl)
            )

          in

          let body_term = translate_expr expr tbl smtEnv in

          Smt_solver.write session (mk_define_fun func_smt_ident arg_sort_list return_sort body_term);
          

        let smtEnv = SmtEnv.pop smtEnv in

        let (func_trnsl: SmtEnv.func_trnsl) = {
          func_symbol = func_smt_ident;
          func_args = sort_list;
          func_return = return_sort;
        } in

        let smtEnv = SmtEnv.add smtEnv fully_qualified_name (Func func_trnsl) in

        smtEnv, session

      )

    )
    | Invariant
    | Pred -> 
      let smtEnv, session = initialize_pred func_def tbl smtEnv session in

      smtEnv, session
    | _ -> Error.error_simple "FuncDef can only be a func/invariant/pred, not proc/lemma"
    )
  )

  | ProcDef proc_def ->
    check_proc_def proc_def tbl smtEnv session