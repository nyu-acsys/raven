open Base
open Ast
open ExtApi
open Util

module ErrorCreditsExt (Cont : Ext) = struct

  let lib_source = Some ("errorCreditsLib.rav", [%blob "errorCreditsLib.rav"])

  module EC_Predefs = struct
    let ec_lib_module_ident = Ident.make Loc.dummy "ErrorCreds" 0
    let ec_lib_field = Ident.make Loc.dummy "error_cred" 0
    let ec_ref = Ident.make Loc.dummy "$errLoc" 0
    let error_module_qi = QualIdent.make [Predefs.lib_ident] ec_lib_module_ident
    let error_field_qi = QualIdent.append error_module_qi ec_lib_field
  end

  let local_vars = [
    (Type.mk_var_decl ~const:true ~ghost:true EC_Predefs.ec_ref Type.ref);
  ]

  type Expr.expr_ext +=
    | ErrorCreds

  type Stmt.stmt_ext +=
      (* args: lhs, N 
        `EC_Rand is_init` generates a random value `x` from `0` to `N-1` which is bound to `lhs`.
      *)
    | EC_Rand of bool

      (* args: lhs, N, errorVal.
        `EC_RandVal is_init` generates a random value `x` from `0` to `N-1` which is bound to `lhs`, and consumes enough error credits (1/N) to ensure that the value `x` will not be equal to `errorVal`. 
      *)
    | EC_RandVal of bool

    (* args: lhs, N, ec, errFn_arg, errFn_def.
        `EC_RandFn is_init` generates a random value `x` from `0` to `N-1` which is bound to `lhs`. It consumes `ec` error credits, and distributes them according to the `errorFn_def`. It also checks that the function definition is sound wrt `ec`, ie in expectation it requires exactly `ec` error credits. The `errorFn_arg` is to simply bind the argument of `errorFn_def`.
    *)
    | EC_RandFn of bool

    (* args: lhs, N, ls.
        `EC_RandList (is_init, tp)` generates a random value `x` from `0` to `N-1` which is bound to `lhs`. It consumes sufficient error credits ((length ls)/N) to ensure that the value `x` will not be in the list `ls` of type Library.List[tp].
    *)
    | EC_RandList of bool

    | EC_Contra

  (* AstDef *)
  let type_ext_to_name = Cont.type_ext_to_name

  let expr_ext_to_string expr_ext =
    match expr_ext with 
    | ErrorCreds -> "-*-"
    | _ -> Cont.expr_ext_to_string expr_ext

  let pr_stmt_ext ppf ext expr_list = 
    let open Stdlib.Format in
    match ext, expr_list with
    | EC_Rand _, [lhs_expr; n_expr] ->
      fprintf ppf "@[<2>[EXT]%a@ :=@ %s(%a)@]" Expr.pr lhs_expr "Rand" Expr.pr n_expr
    | EC_RandVal _, [lhs_expr; n_expr; errorVal] ->
      fprintf ppf "@[<2>[EXT]%a@ :=@ %s(%a; %s:≠%a)@]" Expr.pr lhs_expr "Rand" Expr.pr n_expr "ECVal" Expr.pr errorVal
    | EC_RandFn _, [lhs_expr; n_expr; ec_expr; errFn_arg; errFn_def] -> 
      fprintf ppf "@[<2>[EXT]%a@ :=@ %s(%a; %s:%s(%a), %a ==> %a)@]" Expr.pr lhs_expr "Rand" Expr.pr n_expr "ECFn" "-*-" Expr.pr ec_expr Expr.pr errFn_arg Expr.pr errFn_def
    | EC_RandList _, [lhs_expr; n_expr; ls_expr] -> 
      fprintf ppf "@[<2>[EXT]%a@ :=@ %s(%a; %s: !in%a)@]" Expr.pr lhs_expr "Rand" Expr.pr n_expr "ECList" Expr.pr ls_expr
    | EC_Contra, [] -> 
      fprintf ppf "@[<2>[EXT]EC_Contra@]"
    | _ -> Cont.pr_stmt_ext ppf ext expr_list

  let stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | EC_Rand _ | EC_RandVal _ | EC_RandFn _ | EC_RandList _ | EC_Contra -> Set.empty (module QualIdent)
    | _ -> Cont.stmt_ext_symbols stmt_ext

  let stmt_ext_local_vars_modified stmt_ext exprs =
    match stmt_ext, exprs with
    | EC_Rand _, [lhs_expr; n_expr] ->
      let lhs_qi = Expr.to_qual_ident lhs_expr in
      if QualIdent.is_local lhs_qi then [QualIdent.to_ident lhs_qi] else []
    | EC_RandVal _, [lhs_expr; n_expr; errorVal] -> 
      let lhs_qi = Expr.to_qual_ident lhs_expr in
      if QualIdent.is_local lhs_qi then [QualIdent.to_ident lhs_qi] else []
    | EC_RandFn _, [lhs_expr; n_expr; ec_expr; errFn_arg; errFn_def] ->
      let lhs_qi = Expr.to_qual_ident lhs_expr in
      if QualIdent.is_local lhs_qi then [QualIdent.to_ident lhs_qi] else []
    | EC_RandList _, [lhs_expr; n_expr; ls_expr] ->
      let lhs_qi = Expr.to_qual_ident lhs_expr in
      if QualIdent.is_local lhs_qi then [QualIdent.to_ident lhs_qi] else []
    | EC_Contra, [] -> []
    | _ -> Cont.stmt_ext_local_vars_modified stmt_ext exprs
  
  let stmt_ext_fields_accessed stmt_ext exprs = 
    match stmt_ext, exprs with
    | EC_Rand _, _ -> []
    | (EC_RandFn _ | EC_RandList _ | EC_RandVal _ | EC_Contra), _ -> 
      [EC_Predefs.error_field_qi]
    | _ -> Cont.stmt_ext_fields_accessed stmt_ext exprs

  (* Typing *)
  let type_check_type_expr = Cont.type_check_type_expr


  let type_check_expr (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr : Expr.expr_attr) (expected_typ: type_expr) (type_check_expr_functs: type_check_expr_functs) = 
    let open Rewriter.Syntax in
    match expr_ext, expr_list with
    | ErrorCreds, [ec_val] ->
      let* expr_arg = type_check_expr_functs.process_expr ec_val Type.real in
      type_check_expr_functs.check_and_set 
      (App (ExprExt ErrorCreds, [expr_arg], expr_attr)) Type.perm Type.perm Type.perm

    | ErrorCreds, _ ->
      Error.type_error expr_attr.expr_loc "Incorrect number of arguments for ErrorCredits expression"

    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ type_check_expr_functs

  

  let type_check_stmt call_decl (stmt_ext : Stmt.stmt_ext) (expr_list: expr list) (stmt_loc: Loc.t) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : ExtApi.type_check_stmt_functs)
  :
      (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t = 
    let open Rewriter.Syntax in
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    match stmt_ext, expr_list with
    | EC_Rand is_init, [lhs_expr; n_expr] ->
      let* lhs_qual_ident, var_decl = type_check_stmt_functs.get_assign_lhs (Expr.to_qual_ident lhs_expr) ~is_init in

      let* var_type_expanded = type_check_stmt_functs.expand_type_expr var_decl.var_type in

      if Type.(not (var_type_expanded = Type.int)) then
        type_check_stmt_functs.type_mismatch_error stmt_loc Type.int var_decl.var_type
      else
        let* n_expr = type_check_stmt_functs.disambiguate_process_expr n_expr Type.int disam_tbl in

        Rewriter.return (Stmt.StmtExt (EC_Rand is_init, [Expr.from_var_decl var_decl; n_expr]), disam_tbl)

    | EC_Rand is_init, _ ->
      Error.type_error stmt_loc "Incorrect number of arguments for EC_Rand()"
    
    | EC_RandVal is_init, [lhs_expr; n_expr; errorVal] -> 
      let* lhs_qual_ident, var_decl = type_check_stmt_functs.get_assign_lhs (Expr.to_qual_ident lhs_expr) ~is_init in

      let* var_type_expanded = type_check_stmt_functs.expand_type_expr var_decl.var_type in

      if Type.(not (var_type_expanded = Type.int)) then
        type_check_stmt_functs.type_mismatch_error stmt_loc Type.int var_decl.var_type
      else
        let* n_expr = type_check_stmt_functs.disambiguate_process_expr n_expr Type.int disam_tbl in
        let* errorVal = type_check_stmt_functs.disambiguate_process_expr errorVal Type.int disam_tbl in

        Rewriter.return (Stmt.StmtExt (EC_RandVal is_init, [Expr.from_var_decl var_decl; n_expr; errorVal]), disam_tbl)
      
    | EC_RandVal _, _ ->
      Error.type_error stmt_loc "Incorrect number of arguments for EC_RandVal()"

    | EC_RandFn is_init, [lhs_expr; n_expr; ec_expr; errFn_arg; errFn_def] ->
      let* lhs_qual_ident, var_decl = type_check_stmt_functs.get_assign_lhs (Expr.to_qual_ident lhs_expr) ~is_init in

      let* var_type_expanded = type_check_stmt_functs.expand_type_expr var_decl.var_type in

      if Type.(not (var_type_expanded = Type.int)) then
        type_check_stmt_functs.type_mismatch_error stmt_loc Type.int var_decl.var_type
      else
        let* n_expr = type_check_stmt_functs.disambiguate_process_expr n_expr Type.int disam_tbl in
        let* ec_expr = type_check_stmt_functs.disambiguate_process_expr ec_expr Type.real disam_tbl in

        if not (Expr.is_ident errFn_arg) then
          Error.type_error stmt_loc "Expected an ident as error function argument."
        else
          let fn_arg_var_decl = Type.mk_var_decl ~ghost:false (Expr.to_ident errFn_arg) ~loc:stmt_loc Type.int in

          let disam_tbl = ProgUtils.DisambiguationTbl.push disam_tbl in
          let fn_arg_var_decl, disam_tbl = type_check_stmt_functs.disam_tbl_add_var_decl fn_arg_var_decl disam_tbl in

          let* _ = Rewriter.introduce_symbol 
            (VarDef { var_decl = fn_arg_var_decl; var_init = None})
          in
          (* let errFn_def = Expr.alpha_renaming errFn_def (Map.add_exn ~key:(QualIdent.from_ident (Expr.to_ident errFn_arg)) ~data:(Expr.from_var_decl fn_arg_var_decl) (Map.empty (module QualIdent)) ) in *)
          Logs.debug (fun m -> m "ErrorCreditsExt.type_check_stmt: fn_arg_var_decl = %a; errFn_def= %a;\nDisamTbl:%a" Type.pr_var_decl fn_arg_var_decl Expr.pr errFn_def ProgUtils.DisambiguationTbl.pr disam_tbl);
          let* errFn_def = type_check_stmt_functs.disambiguate_process_expr errFn_def Type.real disam_tbl in

          let disam_tbl = ProgUtils.DisambiguationTbl.pop disam_tbl in

          Rewriter.return (Stmt.StmtExt (EC_RandFn is_init, [Expr.from_var_decl var_decl; n_expr; ec_expr; (Expr.from_var_decl fn_arg_var_decl); errFn_def ]), disam_tbl)

    | EC_RandFn _, _ ->
      Error.type_error stmt_loc "Incorrect number of arguments for EC_RandFn()"

    | EC_RandList is_init, [lhs_expr; n_expr; ls_expr] ->
      let* lhs_qual_ident, var_decl = type_check_stmt_functs.get_assign_lhs (Expr.to_qual_ident lhs_expr) ~is_init in

      let* var_type_expanded = type_check_stmt_functs.expand_type_expr var_decl.var_type in

      if Type.(not (var_type_expanded = Type.int)) then
        type_check_stmt_functs.type_mismatch_error stmt_loc Type.int var_decl.var_type
      else
        let* n_expr = type_check_stmt_functs.disambiguate_process_expr n_expr Type.int disam_tbl in
        
        let* ls_expr = type_check_stmt_functs.disambiguate_process_expr ls_expr (Type.any) disam_tbl in
        let ls_expr_type = Expr.to_type ls_expr in
        let* _ = match ls_expr_type with
        | Type.App (Var v, [], _) ->
          let tp_module_qi = QualIdent.pop v in

          (* ToDo: Add more robust type-checking to ensure only integer list types are allowed.
            At present, only module directly instantiated as `module _ = Library.List[...]` are allowed.
            Checks for underlying type being an Int are also a bit hacky.
          *)
          let* (tp_module_symbol_init_qi, _, _) = Rewriter.find tp_module_qi in
          let* tp_module = Rewriter.find_and_reify_module tp_module_qi in

          (* Logs.debug (fun m -> m "tp_module_symbol = %a, %a" QualIdent.pr tp_module_symbol_init_qi Module.pr tp_module); *)

          if (QualIdent.(tp_module_symbol_init_qi = Predefs.lib_list_mod_qual_ident)) then
            let* head_destr = Rewriter.find_and_reify (QualIdent.append tp_module_qi (Predefs.lib_list_head_destr_ident)) in
            let* base_type = match head_destr with
              | DestrDef destr -> type_check_stmt_functs.expand_type_expr destr.destr_return_type
              | _ -> Error.type_error (Expr.to_loc ls_expr) "Expected a `head` destr for given list expr"
            in

            if Type.(base_type = Type.int) then
              Rewriter.return Type.unit
            else 
                Error.type_error (Expr.to_loc ls_expr) "Expected an Integer list type for ECList"
          else 
            Error.type_error (Expr.to_loc ls_expr) "Expected an integer List type for ECList"
        | _ -> 
          Error.type_error (Expr.to_loc ls_expr) "Expected a integer list type for ECList"
        in
        
        Rewriter.return (Stmt.StmtExt (EC_RandList is_init, [Expr.from_var_decl var_decl; n_expr; ls_expr]), disam_tbl)
    | EC_RandList _, _ ->
      Error.type_error stmt_loc "Incorrect number of arguments for EC_RandList()"

    | EC_Contra, [] ->
      Rewriter.return ( Stmt.StmtExt (EC_Contra, []), disam_tbl)

    | EC_Contra, _ ->
      Error.type_error stmt_loc "Incorrect number of arguments for EC_Contra()"

    | _ -> Cont.type_check_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl type_check_stmt_functs


  let lib_fraction_ident = Ident.make Loc.dummy "Fraction" 0
  let lib_fraction_frac_constr_ident = Ident.make Loc.dummy "frac" 0

  (* Rewrites *)
  let rewrite_type_ext = Cont.rewrite_type_ext
  
  let rewrite_expr_ext (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr: Expr.expr_attr) = 
    let open Rewriter.Syntax in
    let loc = expr_attr.expr_loc in

    match expr_ext, expr_list with

    | ErrorCreds, [ec] ->
      let* ec_ref_var_def = Rewriter.find_and_reify_var (QualIdent.from_ident EC_Predefs.ec_ref) in
      let* ec_field_qi = Rewriter.resolve EC_Predefs.error_field_qi in
      let* ec_field = Rewriter.find_and_reify_field ec_field_qi in

      let* lib_fraction_mod_qual_ident = Rewriter.resolve (QualIdent.from_list [Predefs.lib_ident; lib_fraction_ident]) in

      let* lib_fraction_frac_constr_qi = Rewriter.resolve (QualIdent.append lib_fraction_mod_qual_ident lib_fraction_frac_constr_ident) in
      let* lib_fraction_frac_constr_symbol = Rewriter.find_and_reify lib_fraction_frac_constr_qi in
      let constr_decl =
        match lib_fraction_frac_constr_symbol with
        | ConstrDef constr -> constr
        | _ -> Error.type_error loc "Expected Library.Fraction.frac data constructor"
      in

      let own_expr = Expr.mk_app ~loc ~typ:Type.perm Own 
        [ Expr.from_var_decl ec_ref_var_def.var_decl; 
          Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
          Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [ec]
        ] in

      Rewriter.return own_expr

    | _ -> Cont.rewrite_expr_ext expr_ext expr_list expr_attr

  let rewrite_stmt_ext (stmt_ext: Stmt.stmt_ext) (expr_list: expr list) loc: Stmt.t Rewriter.t =
    let open Rewriter.Syntax in

    let* ec_ref_var_def = Rewriter.find_and_reify_var (QualIdent.from_ident EC_Predefs.ec_ref) in
    let* ec_field_qi = Rewriter.resolve EC_Predefs.error_field_qi in
    let* ec_field = Rewriter.find_and_reify_field ec_field_qi in

    let* lib_fraction_mod_qual_ident = Rewriter.resolve (QualIdent.from_list [Predefs.lib_ident; lib_fraction_ident]) in

    let* lib_fraction_frac_constr_qi = Rewriter.resolve (QualIdent.append lib_fraction_mod_qual_ident lib_fraction_frac_constr_ident) in
    let* lib_fraction_frac_constr_symbol = Rewriter.find_and_reify lib_fraction_frac_constr_qi in
    let constr_decl =
      match lib_fraction_frac_constr_symbol with
      | ConstrDef constr -> constr
      | _ -> Error.type_error loc "Expected Library.Fraction.frac data constructor"
    in

    match stmt_ext, expr_list with
    | EC_Rand is_init, [lhs_expr; n_expr] ->
      let havoc_stmt = Stmt.mk_havoc ~loc ~is_init (Expr.to_qual_ident lhs_expr) in

      let inhale_stmt = 
        Stmt.mk_inhale_expr
          ~cmnt:("EC_RandVal postcond")
          ~loc
          (Expr.mk_and ~loc 
          [ Expr.mk_app ~typ:Type.bool Leq [(Expr.mk_int 0); lhs_expr];
            Expr.mk_app ~typ:Type.bool Lt [lhs_expr; n_expr];
          ])
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc [havoc_stmt; inhale_stmt])

    | EC_RandVal is_init, [lhs_expr; n_expr; errorVal] -> 
      let havoc_stmt = Stmt.mk_havoc ~loc ~is_init (Expr.to_qual_ident lhs_expr) in

      let exhale_stmt = 
        let error = 
          (Error.Verification,
            loc,
            "Not enough error credits to ensure random value does not match given value"
          ) in
        Stmt.mk_exhale_expr ~loc 
        ~cmnt:("EC_RandVal precond")
        ~spec_error:[ Stmt.mk_const_spec_error error ]
        (Expr.mk_app ~loc ~typ:Type.perm Expr.Own 
        [ Expr.from_var_decl ec_ref_var_def.var_decl;
          Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
          Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [Expr.mk_app ~typ:Type.real Div [Expr.mk_int 1; n_expr]]
        ])
      in

      let inhale_stmt1 = 
        Stmt.mk_inhale_expr
          ~cmnt:("EC_RandVal postcond")
          ~loc
          (Expr.mk_and ~loc 
          [ Expr.mk_app ~typ:Type.bool Leq [(Expr.mk_int 0); lhs_expr];
            Expr.mk_app ~typ:Type.bool Lt [lhs_expr; n_expr];
          ])
      in

      let inhale_stmt2 = 
        Stmt.mk_inhale_expr
          ~cmnt:("EC_RandVal postcond")
          ~loc
          (Expr.mk_not (Expr.mk_app ~typ:Type.bool Eq [lhs_expr; errorVal]))
      in


      Rewriter.return (Stmt.mk_block_stmt ~loc [havoc_stmt; exhale_stmt; inhale_stmt1; inhale_stmt2])

    | EC_RandFn is_init, [lhs_expr; n_expr; ec_expr; errFn_arg; errFn_def] ->
      let havoc_stmt = Stmt.mk_havoc ~loc ~is_init (Expr.to_qual_ident lhs_expr)

      in

      let* ( err_expr_var_decls, sum_func_arg_var_decls, sum_func_arg_renaming_map ) = 
        let err_expr_locals = (Expr.local_vars errFn_def) in
        let err_expr_locals = Set.remove err_expr_locals (Expr.to_ident errFn_arg) in
        let err_expr_locals = (Expr.to_ident errFn_arg) :: Set.to_list err_expr_locals in

        let* err_expr_var_decls = Rewriter.List.map err_expr_locals ~f:(fun v -> 
          let+ var_def = Rewriter.find_and_reify_var (QualIdent.from_ident v) in 
          var_def.var_decl) in

        (* redefined err_expr_locals for uniqueness *)
        let func_arg_var_decls =
          List.map err_expr_var_decls ~f:(fun var_decl ->
              let new_var_name =
                Ident.fresh loc var_decl.var_name.ident_name
              in
              Logs.debug (fun m ->
                  m "Loop old_var_name: %a" Ident.pr var_decl.var_name);
              Logs.debug (fun m ->
                  m "Loop new_var_name: %a" Ident.pr new_var_name);
              let new_new_var_name =
                Ident.fresh loc var_decl.var_name.ident_name
              in
              Logs.debug (fun m ->
                  m "Loop new_new_var_name: %a" Ident.pr new_new_var_name);
              { var_decl with var_name = new_var_name })
        in
 
        let func_arg_renaming_map =
          List.fold2_exn err_expr_var_decls func_arg_var_decls
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map old_var_decl new_var_decl ->
              Map.add_exn map
                ~key:(QualIdent.from_ident old_var_decl.var_name)
                ~data:(Expr.from_var_decl new_var_decl))
        in
      
      Rewriter.return ( err_expr_var_decls, func_arg_var_decls, func_arg_renaming_map)
      in

      let* sum_func_name = 
        let+ proc_name = Rewriter.current_scope_id in
        Ident.fresh loc (proc_name.qual_base.ident_name ^ "$errFnSumToN")
      in

      let sum_func_decl = {
        Callable.call_decl_kind = Func;
        call_decl_name = sum_func_name;
        call_decl_formals = sum_func_arg_var_decls;
        call_decl_returns = [Type.mk_var_decl ~loc (Ident.fresh loc "ret") Type.real];
        call_decl_locals = [];
        call_decl_precond = [];
        call_decl_postcond = [];
        call_decl_is_free = false;
        call_decl_is_auto = false;
        call_decl_mask = None;
        call_decl_loc = loc;
      } in

      let sum_func_body = 
        let ind_arg = List.hd_exn sum_func_arg_var_decls in

        (* e < 0 ? 0 : sum_func(e-1, ...) + errFn_def *)
        Expr.mk_ite ~loc 
          (Expr.mk_app ~loc ~typ:Type.bool Lt [(Expr.from_var_decl ind_arg); (Expr.mk_int 0)])
          (Expr.mk_real ~loc 0.0)
          (Expr.mk_app ~loc ~typ:Type.real Plus [
            (Expr.mk_app ~loc ~typ:Type.real (Expr.Var (QualIdent.from_ident sum_func_name)) 
              ((Expr.mk_app ~loc ~typ:Type.int Minus [Expr.from_var_decl ind_arg ; Expr.mk_int 1]) :: (List.map (List.tl_exn sum_func_arg_var_decls) ~f:(Expr.from_var_decl)))
            );
            Expr.alpha_renaming errFn_def sum_func_arg_renaming_map
          ])

      in

      let sum_func_symbol =
        let call_def = Callable.{
          call_decl = sum_func_decl;
          call_def = FuncDef {func_body = Some sum_func_body}
        }
        in
      Module.CallDef call_def

      in

      Logs.debug (fun m ->
        m "ErrorCreditsExt.rewrite_stmt_ext: Pre-typecheck sum_func_symbol:\n %a"
          Symbol.pr sum_func_symbol);

      let* _ =
        Rewriter.introduce_typecheck_symbol' ~loc sum_func_symbol
      in

      let* sum_func_qi = Rewriter.resolve (QualIdent.from_ident sum_func_name) in

      let check_valid_stmt1 = 
        let error = 
          (Error.Verification,
            loc,
            "Error function should always be greater than or equal to 0"
          ) in

        let ind_arg = List.hd_exn sum_func_arg_var_decls in
        let renaming_map = Map.add_exn (Map.empty (module QualIdent)) ~key:(Expr.to_qual_ident errFn_arg) ~data:(Expr.from_var_decl ind_arg) in

        Stmt.mk_exhale_expr ~loc 
        ~cmnt:("EC_RandFn positivity check")
        ~spec_error:[ Stmt.mk_const_spec_error error]
        (Expr.mk_binder ~loc ~typ:Type.bool Forall [ind_arg] 
          (Expr.mk_app ~loc ~typ:Type.bool Geq [
            Expr.alpha_renaming errFn_def renaming_map; 
            Expr.mk_real 0.0])
        )
      in

      let check_valid_stmt2 =
        let error = 
          (Error.Verification,
            loc,
            "Error function does not preserve expected error; function defined incorrectly"
          ) in
        Stmt.mk_exhale_expr ~loc 
        ~cmnt:("EC_RandFn validity check")
        ~spec_error:[ Stmt.mk_const_spec_error error]
        (Expr.mk_eq ~loc
          (Expr.mk_app ~typ:Type.real ~loc Div [
            (Expr.mk_app ~typ:Type.real ~loc (Expr.Var sum_func_qi) 
              ((Expr.mk_app ~loc ~typ:Type.int Minus [n_expr; Expr.mk_int 1]) :: (List.map (List.tl_exn err_expr_var_decls) ~f:(Expr.from_var_decl)))); 
            n_expr
          ])

          ec_expr
        )
      in

      let exhale_stmt = 
        let error = 
          (Error.Verification,
            loc,
            "Not enough error credits to ensure random value does not match given value"
          ) in
        Stmt.mk_exhale_expr ~loc 
        ~cmnt:("EC_RandFn precond")
        ~spec_error:[ Stmt.mk_const_spec_error error ]
        (Expr.mk_app ~loc ~typ:Type.perm Expr.Own 
        [ Expr.from_var_decl ec_ref_var_def.var_decl;
          Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
          Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [ec_expr]
        ])
      in

      let inhale_stmt1 = 
        Stmt.mk_inhale_expr
          ~cmnt:("EC_RandFn postcond")
          ~loc
          (Expr.mk_and ~loc 
          [ Expr.mk_app ~typ:Type.bool Leq [(Expr.mk_int 0); lhs_expr];
            Expr.mk_app ~typ:Type.bool Lt [lhs_expr; n_expr];
          ])
      in

      let inhale_stmt2 = 
        let renaming_map = Map.add_exn (Map.empty (module QualIdent)) ~key:(Expr.to_qual_ident errFn_arg) ~data:(lhs_expr) in

        Stmt.mk_inhale_expr ~loc
          ~cmnt:("EC_RandFn postcond")
          (Expr.mk_app ~loc ~typ:Type.perm Expr.Own 
          [ Expr.from_var_decl ec_ref_var_def.var_decl;
            Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
            Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [Expr.alpha_renaming errFn_def renaming_map]
          ])
      in

      Logs.debug (fun m ->
        m "ErrorCreditsExt.rewrite_stmt_ext: Done rewriting EC_RandFn; output: %a" Stmt.pr (Stmt.mk_block_stmt ~loc [check_valid_stmt1; check_valid_stmt2; exhale_stmt; havoc_stmt; inhale_stmt1; inhale_stmt2]));

      Rewriter.return (Stmt.mk_block_stmt ~loc [check_valid_stmt1; check_valid_stmt2; exhale_stmt; havoc_stmt; inhale_stmt1; inhale_stmt2])

    | EC_RandList is_init, [lhs_expr; n_expr; ls_expr] ->
      let havoc_stmt = Stmt.mk_havoc ~loc ~is_init (Expr.to_qual_ident lhs_expr) in

      let ls_mod_qi = match Expr.to_type ls_expr with
        | App ((Var ls_typ_qi), [], _) -> QualIdent.pop ls_typ_qi
        | _ -> Error.type_error loc "Expected a var type referring to list module for ls_expr"
      in

      let exhale_stmt = 
        let error = 
          (Error.Verification,
            loc,
            "Not enough error credits to ensure random value does lie in given list"
          ) in
        Stmt.mk_exhale_expr ~loc 
        ~cmnt:("EC_RandList precond")
        ~spec_error:[ Stmt.mk_const_spec_error error ]
        (Expr.mk_app ~loc ~typ:Type.perm Expr.Own 
        [ Expr.from_var_decl ec_ref_var_def.var_decl;
          Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
          Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [
            Expr.mk_app ~typ:Type.real Mult [
              (Expr.mk_app ~loc ~typ:Type.int (Var (QualIdent.append ls_mod_qi Predefs.lib_list_len_ident)) [ls_expr]) ;(Expr.mk_app ~typ:Type.real Div [Expr.mk_int 1; n_expr])
            ]
          ]
        ])
      in

      let inhale_stmt1 = 
        Stmt.mk_inhale_expr
          ~cmnt:("EC_RandList postcond")
          ~loc
          (Expr.mk_and ~loc 
          [ Expr.mk_app ~typ:Type.bool Leq [(Expr.mk_int 0); lhs_expr];
            Expr.mk_app ~typ:Type.bool Lt [lhs_expr; n_expr];
          ])
      in

      let inhale_stmt2 = 
        Stmt.mk_inhale_expr
          ~cmnt:("EC_RandList postcond")
          ~loc
          (Expr.mk_not (Expr.mk_app ~typ:Type.bool (Var (QualIdent.append ls_mod_qi Predefs.lib_list_is_in_ident)) [ls_expr; lhs_expr]))
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc [havoc_stmt; exhale_stmt; inhale_stmt1; inhale_stmt2])

    | EC_Contra, [] ->
      let exhale_stmt = 
        let error = 
          (Error.Verification,
            loc,
            "Not enough error credits to ensure false"
          ) in
        Stmt.mk_exhale_expr ~loc 
        ~cmnt:("EC_Contra precond")
        ~spec_error:[ Stmt.mk_const_spec_error error ]
        (Expr.mk_app ~loc ~typ:Type.perm Expr.Own 
        [ Expr.from_var_decl ec_ref_var_def.var_decl;
          Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
          Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [ Expr.mk_real 1.0 ]
        ])
      in

      let inhale_stmt = 
        Stmt.mk_inhale_expr ~loc
        ~cmnt:("EC_Contra postcond")
        (Expr.mk_bool false)
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc [exhale_stmt; inhale_stmt])
    
    | _ -> Cont.rewrite_stmt_ext stmt_ext expr_list loc


  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
  let ext_local_vars = local_vars @ Cont.ext_local_vars
end