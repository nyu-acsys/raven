open Base
open Ast
open ExtApi
open Util

(** Here we implement an extension that adds support for reasoning about Error-credits, and probablistic programs. This extension can be enabled with the:
  `--extension eris`
command-line argument.

This extension introduces:
  - `ErrorCreds` expression: these represent error credit resources
  - `lhs := EC.rand(n);` command: to generate a random number between `0` and `n-1`
  - `lhs := EC.rand(n; ECVal: !=k);` command: to generate a random number between `0` and `n-1`; then it spends enough error credits and ensures that the generated number is not equal to `k`
  - `lhs := EC.rand(n; ECFn: EC.error(e), x ==> body(x));` command: to generate a random number between `0` and `n-1`; then it redistrbutes `e` error credits according to the function defined by `x ==> body(x)`.
  - `lhs := EC.rand(n; ECList: !in ls);` command: to generate a random number between `0` and `n-1`; then it spends enough error credits and ensures that the generated number is not in the list `ls`.
  - `EC.contra()` command: to abort the proof when we get ownership of `EC.error(1.0)`.

*)


module ErrorCreditsExt (Cont : ListApi) = struct
  (* Custom library to be included as part of this extension. The contents of this file are appended to Raven's `Library` module. *)
  let lib_source = Some ("errorCreditsLib.rav", [%blob "errorCreditsLib.rav"])

  (* Hard-coding ident constants from `errorCreditsLib.rav` *)
  module EC_Predefs = struct
    let ec_lib_module_ident = Ident.make Loc.dummy "ErrorCreds" 0
    let ec_lib_field = Ident.make Loc.dummy "error_cred" 0

    let ec_loc_ident = Ident.make Loc.dummy "error_loc" 0

    let error_module_qi = QualIdent.make [Predefs.lib_ident] ec_lib_module_ident
    let error_field_qi = QualIdent.append error_module_qi ec_lib_field

    let error_loc_qi = QualIdent.append error_module_qi ec_loc_ident
  end

  (* Not defining any local variables. *)
  let local_vars = []

  (* Expression for ErrorCredits *)
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

    (* Command for EC.contra() *)
    | EC_Contra

  (* Forwarding List module API  *)
  module ListFns = Cont.ListFns

  (* AstDef *)
  let type_ext_to_name = Cont.type_ext_to_name

  let expr_ext_to_string expr_ext =
    match expr_ext with 
    | ErrorCreds -> "EC.error"
    | _ -> Cont.expr_ext_to_string expr_ext

  let pr_stmt_ext ppf ext expr_list = 
    let open Stdlib.Format in
    match ext, expr_list with
    | EC_Rand _, [lhs_expr; n_expr] ->
      fprintf ppf "@[<2>[EXT]%a@ :=@ %s(%a)@]" Expr.pr lhs_expr "Rand" Expr.pr n_expr
    | EC_RandVal _, [lhs_expr; n_expr; errorVal] ->
      fprintf ppf "@[<2>[EXT]%a@ :=@ %s(%a; %s:≠%a)@]" Expr.pr lhs_expr "Rand" Expr.pr n_expr "ECVal" Expr.pr errorVal
    | EC_RandFn _, [lhs_expr; n_expr; ec_expr; errFn_arg; errFn_def] -> 
      fprintf ppf "@[<2>[EXT]%a@ :=@ %s(%a; %s:%s(%a), %a ==> %a)@]" Expr.pr lhs_expr "Rand" Expr.pr n_expr "ECFn" "EC.error" Expr.pr ec_expr Expr.pr errFn_arg Expr.pr errFn_def
    | EC_RandList _, [lhs_expr; n_expr; ls_expr] -> 
      fprintf ppf "@[<2>[EXT]%a@ :=@ %s(%a; %s: !in%a)@]" Expr.pr lhs_expr "Rand" Expr.pr n_expr "ECList" Expr.pr ls_expr
    | EC_Contra, [] -> 
      fprintf ppf "@[<2>[EXT]EC_Contra@]"
    | _ -> Cont.pr_stmt_ext ppf ext expr_list

  (* Expected to be mostly empty. *)
  let stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | EC_Rand _ | EC_RandVal _ | EC_RandFn _ | EC_RandList _ | EC_Contra -> Set.empty (module QualIdent)
    | _ -> Cont.stmt_ext_symbols stmt_ext

  let stmt_ext_local_vars_modified stmt_ext exprs =
    match stmt_ext, exprs with
    | EC_Rand _, [lhs_expr; n_expr] ->
      let lhs_qi = Expr.to_qual_ident lhs_expr in
      (* only the lhs_expr is being modified. If it is a local variable, we return it. *)
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
    (* Normal EC.rand() does not access any resources. *)
    | EC_Rand _, _ -> []
    (* All other function calls interact with the error_field. *)
    | (EC_RandFn _ | EC_RandList _ | EC_RandVal _ | EC_Contra), _ -> 
      [EC_Predefs.error_field_qi]
    | _ -> Cont.stmt_ext_fields_accessed stmt_ext exprs


  (* Rewriter *)
  (* Almost always skipped. Only used with the extension constructor contains a `type_expr`; see Prophecy extension. *)
  let expr_ext_rewrite_types = Cont.expr_ext_rewrite_types
  let stmt_ext_rewrite_types = Cont.stmt_ext_rewrite_types


  (* Typing *)

  (* No new types. *)
  let type_check_type_expr = Cont.type_check_type_expr

  (* Type-checking for ErrorCreds expressions. The underlying expression in the AST that we are type-checking is:
      Expr.App ((ExprExt expr_ext), expr_list, expr_attr)

    expected_typ contains typing hints from the surrounding env, but is often `Type.any`.
  *)
  let type_check_expr (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr : Expr.expr_attr) (expected_typ: type_expr) (type_check_expr_functs: type_check_expr_functs) = 
    let open Rewriter.Syntax in
    match expr_ext, expr_list with
    (* Need to have exactly one argument *)
    | ErrorCreds, [ec_val] ->
      (* Need to have this argument be a `Type.real` *)
      let* expr_arg = type_check_expr_functs.process_expr ec_val (Type.real |> Type.set_ghost_to expected_typ) in
      (* That's it. Call `check_and_set` with:
          `expr; given_typ_lb; given_typ_ub; expected_typ`  
      *)
      type_check_expr_functs.check_and_set 
      (App (ExprExt ErrorCreds, [expr_arg], expr_attr)) Type.perm Type.perm Type.perm

    | ErrorCreds, _ ->
      Error.type_error expr_attr.expr_loc "Incorrect number of arguments for ErrorCredits expression"

    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ type_check_expr_functs


  (* Type-checking statements. The underlying stmt in the AST is represented as:
      Stmt.{ 
        stmt_desc = Basic (StmtExt (stmt_ext, expr_list)); 
        stmt_loc = stmt_loc; 
      }

    `disam_tbl` is a data structure used to disambiguate local variables occuring in different subscopes by assigning a unique `ident_num` to each local variable. There is no need to understand how this works or to manipulate this manually. Some functions require and return this argument, which indicates how this must be used. However, care must be made to update and return this correctly.

    This function returns a `Stmt.basic_stmt_desc`. This is an object like:
      (StmtExt (stmt_ext, expr_list))
    In addition, a `disam_tbl` must be returned.
    `type_check_stmt_functs` is a set of functions from `typing.ml` that are useful for type-checking statements.
  *)
  let type_check_stmt call_decl (stmt_ext : Stmt.stmt_ext) (expr_list: expr list) (stmt_loc: Loc.t) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : ExtApi.type_check_stmt_functs)
  :
      (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t = 
    let open Rewriter.Syntax in
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    match stmt_ext, expr_list with
    (* ```lhs_expr := EC.rand(n_expr);``` *)
    | EC_Rand is_init, [lhs_expr; n_expr] ->
      (* Use existing function `get_assign_lhs` to get variable declarations for variables being assigned to. *)
      let* lhs_qual_ident, var_decl = type_check_stmt_functs.get_assign_lhs (Expr.to_qual_ident lhs_expr) ~is_init in

      (* Call `expand_type_expr` to get the underlying type. *)
      let* var_type_expanded = type_check_stmt_functs.expand_type_expr var_decl.var_type in

      (* Underlying type should be Int, otherwise, type-error. *)
      if Type.(not (var_type_expanded = Type.int)) then
        type_check_stmt_functs.type_mismatch_error stmt_loc Type.int var_decl.var_type
      else
        (* If so, then type-check this expression as a `Type.int` *)
        let* n_expr = type_check_stmt_functs.disambiguate_process_expr n_expr Type.int disam_tbl in

        (* That's it. Rebuild the Stmt.basic_stmt_desc; make sure to use the updated and type-checked arguments and not stale copies. *)
        Rewriter.return (Stmt.StmtExt (EC_Rand is_init, [Expr.from_var_decl var_decl; n_expr]), disam_tbl)

    | EC_Rand is_init, _ ->
      Error.type_error stmt_loc "Incorrect number of arguments for EC_Rand()"
    
    (* ```lhs_expr := EC.rand(n_expr; ECVal: != errorVal);``` *)
    | EC_RandVal is_init, [lhs_expr; n_expr; errorVal] -> 
      let* lhs_qual_ident, var_decl = type_check_stmt_functs.get_assign_lhs (Expr.to_qual_ident lhs_expr) ~is_init in

      let* var_type_expanded = type_check_stmt_functs.expand_type_expr var_decl.var_type in

      if Type.(not (var_type_expanded = Type.int)) then
        type_check_stmt_functs.type_mismatch_error stmt_loc Type.int var_decl.var_type
      else
        (* type-check all arguments *)
        let* n_expr = type_check_stmt_functs.disambiguate_process_expr n_expr Type.int disam_tbl in
        let* errorVal = type_check_stmt_functs.disambiguate_process_expr errorVal (Type.int |> Type.set_ghost true) disam_tbl in

        (* Reconstruct type-check `Stmt.basic_stmt_desc` *)
        Rewriter.return (Stmt.StmtExt (EC_RandVal is_init, [Expr.from_var_decl var_decl; n_expr; errorVal]), disam_tbl)
      
    | EC_RandVal _, _ ->
      Error.type_error stmt_loc "Incorrect number of arguments for EC_RandVal()"

    (* ```lhs_expr := EC.rand(n_expr; ECFn; ec_expr, errFn_arg ==> errFn_def)``` *)
    | EC_RandFn is_init, [lhs_expr; n_expr; ec_expr; errFn_arg; errFn_def] ->
      let* lhs_qual_ident, var_decl = type_check_stmt_functs.get_assign_lhs (Expr.to_qual_ident lhs_expr) ~is_init in

      let* var_type_expanded = type_check_stmt_functs.expand_type_expr var_decl.var_type in

      if Type.(not (var_type_expanded = Type.int)) then
        type_check_stmt_functs.type_mismatch_error stmt_loc Type.int var_decl.var_type
      else
        (* Type-check all arguments *)
        let* n_expr = type_check_stmt_functs.disambiguate_process_expr n_expr Type.int disam_tbl in
        let* ec_expr = type_check_stmt_functs.disambiguate_process_expr ec_expr (Type.real |> Type.set_ghost true) disam_tbl in

        (* `errFn_arg` must be an ident. *)
        if not (Expr.is_ident errFn_arg) then
          Error.type_error stmt_loc "Expected an ident as error function argument."
        else
          (* Create a new local variable for `errFn_arg` to be able to type-check function defn *)
          let fn_arg_var_decl = Type.mk_var_decl ~ghost:false (Expr.to_ident errFn_arg) ~loc:stmt_loc Type.int in

          (* "Pushing" to disam_tbl` to allow reuse of variables; not strictly necessary but a quality-of-life improvement. Must remember to "pop" when we're done. *)
          let disam_tbl = ProgUtils.DisambiguationTbl.push disam_tbl in
          (* add the new variable to `disam_tbl`. Update `disam_tbl`. *)
          let fn_arg_var_decl, disam_tbl = type_check_stmt_functs.disam_tbl_add_var_decl fn_arg_var_decl disam_tbl in

          (* add symbol to Raven symbolTbl *)
          let* _ = Rewriter.introduce_symbol 
            (VarDef { var_decl = fn_arg_var_decl; var_init = None})
          in

          (* another log stmt. *)
          Logs.debug (fun m -> m "ErrorCreditsExt.type_check_stmt: fn_arg_var_decl = %a; errFn_def= %a;\nDisamTbl:%a" Type.pr_var_decl fn_arg_var_decl Expr.pr errFn_def ProgUtils.DisambiguationTbl.pr disam_tbl);

          (* After adding new variable to symbolTbl, we are finally ready to type-check the function definition expresion, `errFn_def` *)
          let* errFn_def = type_check_stmt_functs.disambiguate_process_expr errFn_def Type.real disam_tbl in

          (* "Popping" from disam_tbl since we're done. *)
          let disam_tbl = ProgUtils.DisambiguationTbl.pop disam_tbl in

          (* Construct the final `Stmt.basic_stmt_desc` *)
          Rewriter.return (Stmt.StmtExt (EC_RandFn is_init, [Expr.from_var_decl var_decl; n_expr; ec_expr; (Expr.from_var_decl fn_arg_var_decl); errFn_def ]), disam_tbl)

    | EC_RandFn _, _ ->
      Error.type_error stmt_loc "Incorrect number of arguments for EC_RandFn()"

    (* ```lhs_expr := EC.rand(n_expr; ECList: !in ls_expr)``` *)
    | EC_RandList is_init, [lhs_expr; n_expr; ls_expr] ->
      let* lhs_qual_ident, var_decl = type_check_stmt_functs.get_assign_lhs (Expr.to_qual_ident lhs_expr) ~is_init in

      let* var_type_expanded = type_check_stmt_functs.expand_type_expr var_decl.var_type in

      if Type.(not (var_type_expanded = Type.int)) then
        type_check_stmt_functs.type_mismatch_error stmt_loc Type.int var_decl.var_type
      else
        let* n_expr = type_check_stmt_functs.disambiguate_process_expr n_expr Type.int disam_tbl in
        
        
        let* ls_expr = type_check_stmt_functs.disambiguate_process_expr ls_expr (Type.any |> Type.set_ghost true) disam_tbl in
        let ls_expr_type = Expr.to_type ls_expr in
        let* _ = match ls_expr_type with
        (* Doing a little hacky workaround to ensure the type of `ls_expr` is a list expression. *)
        | Type.App (Var v, [], _) ->
          let tp_module_qi = QualIdent.pop v in

          (* ToDo: Add more robust type-checking to ensure only integer list types are allowed.
            At present, only module directly instantiated as `module _ = Library.List[...]` are allowed.
            Checks for underlying type being an Int are also a bit hacky.
          *)
          let* (tp_module_symbol_init_qi, _, _) = Rewriter.find tp_module_qi in
          let* tp_module = Rewriter.find_and_reify_module tp_module_qi in

          (* Logs.debug (fun m -> m "tp_module_symbol = %a, %a" QualIdent.pr tp_module_symbol_init_qi Module.pr tp_module); *)

          (* Essentially, we're checking that a suitable `.hd()` destructor exists in the underlying structure. Because to be honest that's all we need. *)
          if (QualIdent.(tp_module_symbol_init_qi = Predefs.lib_list_mod_qual_ident)) then
            let* head_destr = Rewriter.find_and_reify (QualIdent.append tp_module_qi (Predefs.lib_list_head_destr_ident)) in
            let* base_type = match head_destr with
              | DestrDef destr -> type_check_stmt_functs.expand_type_expr destr.destr_return_type
              | _ -> Error.type_error (Expr.to_loc ls_expr) "Expected a `head` destr for given list expr"
            in

            if Type.(base_type = Type.int) then
              Rewriter.return ()
            else 
                Error.type_error (Expr.to_loc ls_expr) "Expected an Integer list type for ECList"
          else 
            Error.type_error (Expr.to_loc ls_expr) "Expected an integer List type for ECList"

        (* This is the case we use the `List[.]` module. Using `Cons.ListFns.listTpConstr` to ensure it is a List. *)
        | Type.App (TypeExt tp_constr, [elem_typ], _) when Type.compare_type_ext tp_constr (Cont.ListFns.listTpConstr ()) = 0 ->
          if Type.(not (elem_typ = int)) then
            type_check_stmt_functs.type_mismatch_error stmt_loc Type.int elem_typ
          else
            Rewriter.return ()
        | _typ -> 
          Error.type_error (Expr.to_loc ls_expr) ("Expected a integer list type for ECList; found: " ^ (Type.to_string _typ))
        in
        
        Rewriter.return (Stmt.StmtExt (EC_RandList is_init, [Expr.from_var_decl var_decl; n_expr; ls_expr]), disam_tbl)
    | EC_RandList _, _ ->
      Error.type_error stmt_loc "Incorrect number of arguments for EC_RandList()"

    | EC_Contra, [] ->
      Rewriter.return ( Stmt.StmtExt (EC_Contra, []), disam_tbl)

    | EC_Contra, _ ->
      Error.type_error stmt_loc "Incorrect number of arguments for EC_Contra()"

    | _ -> Cont.type_check_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl type_check_stmt_functs


  (* Rewrites *)
  let rewrite_type_ext = Cont.rewrite_type_ext
  
  (* Rewrite expressions. We rewrite the resource 
      `EC.error(ec)` to ~~>
      
      `own(Library.ErrorCreds.error_loc, Library.ErrorCreds.error_cred, Library.Fraction.frac(ec))` *)
  let rewrite_expr_ext (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr: Expr.expr_attr) = 
    let open Rewriter.Syntax in
    let loc = expr_attr.expr_loc in

    match expr_ext, expr_list with
    | ErrorCreds, [ec] ->
      (* Getting the `Library.ErrorCreds.error_loc` variable. *)
      let* ec_ref_var_def = Rewriter.find_and_reify_var EC_Predefs.error_loc_qi in
      let ec_ref_expr = Expr.mk_var ~typ:ec_ref_var_def.var_decl.var_type EC_Predefs.error_loc_qi in
      let* ec_field_qi = Rewriter.resolve EC_Predefs.error_field_qi in
      let* ec_field = Rewriter.find_and_reify_field ec_field_qi in

      (* ```Library.Fraction.frac(ec)``` *)
      let* lib_fraction_frac_constr_qi = Rewriter.resolve (QualIdent.append Predefs.lib_fraction_mod_qual_ident Predefs.lib_fraction_frac_constr_ident) in
      let* lib_fraction_frac_constr_symbol = Rewriter.find_and_reify lib_fraction_frac_constr_qi in
      let constr_decl =
        match lib_fraction_frac_constr_symbol with
        | ConstrDef constr -> constr
        | _ -> Error.type_error loc "Expected Library.Fraction.frac data constructor"
      in

      (* ```own(Library.ErrorCreds.error_loc, Library.ErrorCreds.error_cred, Library.Fraction.frac(ec))``` *)
      let own_expr = Expr.mk_app ~loc ~typ:Type.perm Own 
        [ ec_ref_expr; 
          Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
          Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [ec]
        ] in

      Rewriter.return own_expr

    | _ -> Cont.rewrite_expr_ext expr_ext expr_list expr_attr


  (* Rewriting Statements *)
  let rewrite_stmt_ext (stmt_ext: Stmt.stmt_ext) (expr_list: expr list) loc: Stmt.t Rewriter.t =
    let open Rewriter.Syntax in

    (* Pre-looking up a bunch of different variables used in multiple cases *)
    let* ec_ref_var_def = Rewriter.find_and_reify_var EC_Predefs.error_loc_qi in
    let ec_ref_expr = Expr.mk_var ~typ:ec_ref_var_def.var_decl.var_type EC_Predefs.error_loc_qi in
    let* ec_field_qi = Rewriter.resolve EC_Predefs.error_field_qi in
    let* ec_field = Rewriter.find_and_reify_field ec_field_qi in

    let* lib_fraction_frac_constr_qi = Rewriter.resolve (QualIdent.append Predefs.lib_fraction_mod_qual_ident Predefs.lib_fraction_frac_constr_ident) in
    let* lib_fraction_frac_constr_symbol = Rewriter.find_and_reify lib_fraction_frac_constr_qi in
    let constr_decl =
      match lib_fraction_frac_constr_symbol with
      | ConstrDef constr -> constr
      | _ -> Error.type_error loc "Expected Library.Fraction.frac data constructor"
    in

    match stmt_ext, expr_list with
    (* ```lhs_expr := EC.rand(n_expr);``` *)
    | EC_Rand is_init, [lhs_expr; n_expr] ->
      (* Create statements to encode semantics of `EC.rand()` *)
      let havoc_stmt = Stmt.mk_havoc ~loc ~is_init (Expr.to_qual_ident lhs_expr) in

      (* ```inhale 0 <= lhs_expr < n_expr;``` *)
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

    (* ```lhs_expr := EC.rand(n_expr; ECVal: != errorVal);``` *)
    | EC_RandVal is_init, [lhs_expr; n_expr; errorVal] -> 
      let havoc_stmt = Stmt.mk_havoc ~loc ~is_init (Expr.to_qual_ident lhs_expr) in

      (* ```exhale own(ec_ref, ec_field, Fraction(1 / n_expr))``` *)
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
        [ ec_ref_expr;
          Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
          Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [Expr.mk_app ~typ:Type.real Div [Expr.mk_int 1; n_expr]]
        ])
      in

      (* ```inhale 0 <= lhs_expr < n_expr``` *)
      let inhale_stmt1 = 
        Stmt.mk_inhale_expr
          ~cmnt:("EC_RandVal postcond")
          ~loc
          (Expr.mk_and ~loc 
          [ Expr.mk_app ~typ:Type.bool Leq [(Expr.mk_int 0); lhs_expr];
            Expr.mk_app ~typ:Type.bool Lt [lhs_expr; n_expr];
          ])
      in

      (* ``` lhs_expr != errorVar;``` *)
      let inhale_stmt2 = 
        Stmt.mk_inhale_expr
          ~cmnt:("EC_RandVal postcond")
          ~loc
          (Expr.mk_not (Expr.mk_app ~typ:Type.bool Eq [lhs_expr; errorVal]))
      in


      Rewriter.return (Stmt.mk_block_stmt ~loc [havoc_stmt; exhale_stmt; inhale_stmt1; inhale_stmt2])


    (* ```
        lhs_expr := EC.rand(n_expr; 
          ECFn: EC.error(ec_expr), errFn_arg ==> errFn_def
        );
    ``` *)
    | EC_RandFn is_init, [lhs_expr; n_expr; ec_expr; errFn_arg; errFn_def] ->
      let havoc_stmt = Stmt.mk_havoc ~loc ~is_init (Expr.to_qual_ident lhs_expr)

      in

      (* Here, we are collecting all the free variables occuring in `errFn_def`; these will need to be provided as arguments to the `sumToN()` function that we must define. We also build a renaming_map to be able to easily alpha_rename the body for the function definition. *)
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

      (* Define the function declaration for the `errFnSumToN` function *)
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

      (* Define function body *)
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

      (* Put them together to build symbol *)
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

      (* Add the function symbol to the symbolTbl *)
      let* _ =
        Rewriter.introduce_typecheck_symbol' ~loc sum_func_symbol
      in

      let* sum_func_qi = Rewriter.resolve (QualIdent.from_ident sum_func_name) in

      (* ```exhale forall ind_arg: Int :: errFn_def(ind) >= 0.0``` *)
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

      (* ```exhale errFnSumToN(n-1, <env_vars>) == ec_expr```  *)
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

      (* ```exhale own(ec_ref, ec_field, Fraction.frac(ec_expr))``` *)
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
        [ ec_ref_expr;
          Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
          Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [ec_expr]
        ])
      in

      (* ```inhale 0 <= lhs_expr < n_expr``` *)
      let inhale_stmt1 = 
        Stmt.mk_inhale_expr
          ~cmnt:("EC_RandFn postcond")
          ~loc
          (Expr.mk_and ~loc 
          [ Expr.mk_app ~typ:Type.bool Leq [(Expr.mk_int 0); lhs_expr];
            Expr.mk_app ~typ:Type.bool Lt [lhs_expr; n_expr];
          ])
      in

      (* ```inhale own(ec_ref, ec_field Fraction.frac(errFn_def(lhs_expr)) )``` *)
      let inhale_stmt2 = 
        let renaming_map = Map.add_exn (Map.empty (module QualIdent)) ~key:(Expr.to_qual_ident errFn_arg) ~data:(lhs_expr) in

        Stmt.mk_inhale_expr ~loc
          ~cmnt:("EC_RandFn postcond")
          (Expr.mk_app ~loc ~typ:Type.perm Expr.Own 
          [ ec_ref_expr;
            Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
            Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [Expr.alpha_renaming errFn_def renaming_map]
          ])
      in

      Logs.debug (fun m ->
        m "ErrorCreditsExt.rewrite_stmt_ext: Done rewriting EC_RandFn; output: %a" Stmt.pr (Stmt.mk_block_stmt ~loc [check_valid_stmt1; check_valid_stmt2; exhale_stmt; havoc_stmt; inhale_stmt1; inhale_stmt2]));

      Rewriter.return (Stmt.mk_block_stmt ~loc [check_valid_stmt1; check_valid_stmt2; exhale_stmt; havoc_stmt; inhale_stmt1; inhale_stmt2])

    (* ```lhs_expr := EC.rand(n_expr; ECList: !in ls_expr)``` *)
    | EC_RandList is_init, [lhs_expr; n_expr; ls_expr] ->
      let havoc_stmt = Stmt.mk_havoc ~loc ~is_init (Expr.to_qual_ident lhs_expr) in

      let ls_mod_qi = match Expr.to_type ls_expr with
        | App ((Var ls_typ_qi), [], _) -> QualIdent.pop ls_typ_qi
        | _ -> Error.type_error loc "Expected a var type referring to list module for ls_expr"
      in

      (* ```exhale own(ec_ref, ec_field, Fraction.frac(List.len(ls_expr) / n_expr));``` *)
      let exhale_stmt = 
        let error = 
          (Error.Verification,
            loc,
            "Not enough error credits to ensure random value doesn't lie in given list"
          ) in
        Stmt.mk_exhale_expr ~loc 
        ~cmnt:("EC_RandList precond")
        ~spec_error:[ Stmt.mk_const_spec_error error ]
        (Expr.mk_app ~loc ~typ:Type.perm Expr.Own 
        [ ec_ref_expr;
          Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
          Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [
            Expr.mk_app ~typ:Type.real Div [
              (Expr.mk_app ~loc ~typ:Type.int (Var (QualIdent.append ls_mod_qi Predefs.lib_list_len_ident)) [ls_expr]) ; n_expr
            ]
          ]
        ])
      in

      (* ```inhale 0 <= lhs_expr < n_expr;``` *)
      let inhale_stmt1 = 
        Stmt.mk_inhale_expr
          ~cmnt:("EC_RandList postcond")
          ~loc
          (Expr.mk_and ~loc 
          [ Expr.mk_app ~typ:Type.bool Leq [(Expr.mk_int 0); lhs_expr];
            Expr.mk_app ~typ:Type.bool Lt [lhs_expr; n_expr];
          ])
      in

      (* ```inhale !List.is_in(ls_expr, lhs_expr);``` *)
      let inhale_stmt2 = 
        Stmt.mk_inhale_expr
          ~cmnt:("EC_RandList postcond")
          ~loc
          (Expr.mk_not (Expr.mk_app ~typ:Type.bool (Var (QualIdent.append ls_mod_qi Predefs.lib_list_is_in_ident)) [ls_expr; lhs_expr]))
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc [havoc_stmt; exhale_stmt; inhale_stmt1; inhale_stmt2])

    | EC_Contra, [] ->
      (* ```exhale own(ec_ref, ec_field, Fraction.frac(1.0));``` *)
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
        [ ec_ref_expr;
          Expr.mk_var ~typ:(ec_field.field_type) ec_field_qi;
          Expr.mk_app ~loc ~typ:constr_decl.constr_return_type (DataConstr lib_fraction_frac_constr_qi) [ Expr.mk_real 1.0 ]
        ])
      in

      (* ```inhale false;``` *)
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