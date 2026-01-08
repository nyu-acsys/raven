open Base
open Ast
open ExtApi
open Util

module ListExt (Cont : Ext) = struct
  let lib_source = None
  let local_vars = []

  module ListPredefs = struct
    let list_mod_ident_prefix = "ListExtMod$$"
    let cons_ident = Ident.make Loc.dummy "cons" 0
    let nil_ident = Ident.make Loc.dummy "nil" 0

    let hd_destr_ident = Ident.make Loc.dummy "hd" 0
    let tl_destr_ident = Ident.make Loc.dummy "tl" 0
    
    let len_ident = Ident.make Loc.dummy "len" 0
    let is_in_ident = Ident.make Loc.dummy "is_in" 0
  end

  open ListPredefs

  type Type.type_ext +=
    | ListConstr

  type Expr.expr_ext +=
    | ListExpr of ident


  (* ListApi functions: *)
  let listTpConstr () = ListConstr

  let mk_list_tp loc tp = Type.mk_app ~loc (TypeExt ListConstr) [tp]

  let ls_cons loc hd_expr tl_expr = 
    Expr.mk_app ~loc ~typ:(Expr.to_type tl_expr)
      (ExprExt (ListExpr ListPredefs.cons_ident))
    [hd_expr; tl_expr]

  let ls_nil loc ~elem_typ () = 
    Expr.mk_app ~loc ~typ:(mk_list_tp loc elem_typ)
      (ExprExt (ListExpr ListPredefs.nil_ident))
    []

  let ls_hd loc ls_expr = 
    let elem_type = 
      match (Expr.to_type ls_expr) with
      | Type.App (TypeExt ListConstr, [elem_tp], _) -> elem_tp
      | _ -> Error.type_error loc "[EXT] ListExt: List.hd called on a mistyped argument"
    in
    Expr.mk_app ~loc ~typ:(elem_type) 
      (ExprExt (ListExpr ListPredefs.hd_destr_ident))
    [ls_expr]

  let ls_tl loc ls_expr =
    Expr.mk_app ~loc
    ~typ:(Expr.to_type ls_expr)
    (ExprExt (ListExpr ListPredefs.tl_destr_ident))
    [ ls_expr ]

  let ls_len loc ls_expr =
    Expr.mk_app ~loc
      ~typ:(Type.int)
    (ExprExt (ListExpr ListPredefs.len_ident))
    [ls_expr]

  let mk_list_tp loc tp = Type.mk_app ~loc ~ghost:(Type.is_ghost tp) (TypeExt ListConstr) [tp]

  let list_tp_to_elem_typ tp_expr =
    match tp_expr with
    | Type.App (TypeExt ListConstr, [elem_typ], _) ->
      Some elem_typ
    | Type.App (Var list_tp_qi, [], _) -> 

      let tp_mod_ident =  (QualIdent.pop list_tp_qi).qual_base in

      if String.is_prefix tp_mod_ident.ident_name ~prefix:ListPredefs.list_mod_ident_prefix then
        
        let elem_typ_qi = (QualIdent.append (QualIdent.append (QualIdent.pop list_tp_qi) Predefs.lib_list_arg_mod_ident) Predefs.lib_type_rep_type_ident) in
        Some (
          Type.App (Var elem_typ_qi, [], Type.dummy_attr)
        )
      else
        None
    | _ -> None


  (* AstDef *)
  let type_ext_to_name type_ext =
    match type_ext with 
    | ListConstr -> "List"
    | _ -> 
      Cont.type_ext_to_name type_ext

  let expr_ext_to_string expr_ext =
    match expr_ext with 
    | ListExpr c -> "List." ^ Ident.to_string c 
    | _ -> Cont.expr_ext_to_string expr_ext

  let pr_stmt_ext ppf ext expr_list = 
    match ext, expr_list with
    | _ -> Cont.pr_stmt_ext ppf ext expr_list

  let stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | _ -> Cont.stmt_ext_symbols stmt_ext

  let stmt_ext_local_vars_modified = Cont.stmt_ext_local_vars_modified
  
  let stmt_ext_fields_accessed = Cont.stmt_ext_fields_accessed


  (* Rewriter *)
  let expr_ext_rewrite_types = Cont.expr_ext_rewrite_types
  let stmt_ext_rewrite_types = Cont.stmt_ext_rewrite_types


  (* Typing *)
  let type_check_type_expr (type_ext: Type.type_ext) (type_args: type_expr list) (type_attr: Type.type_attr) (type_check_type_expr_functs: type_check_type_expr_functs) =
    let open Rewriter.Syntax in
    match type_ext, type_args with
    | ListConstr, [elem_typ] ->

      let* elem_typ = type_check_type_expr_functs.process_type_expr elem_typ in
      (Type.mk_app ~loc:type_attr.type_loc (TypeExt ListConstr) [elem_typ]) |> Type.set_ghost_to elem_typ |> Rewriter.return 

    | ListConstr, _ ->
      Error.type_error type_attr.type_loc "[ListExt] List type called with incorrect number of arguments"

    | _ -> Cont.type_check_type_expr type_ext type_args type_attr type_check_type_expr_functs


  let type_check_expr (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr : Expr.expr_attr) (expected_typ: type_expr) (type_check_expr_functs: type_check_expr_functs) = 
    let open Rewriter.Syntax in
    
    match expr_ext, expr_list with
    | ListExpr c, exprs -> begin
      Logs.debug (fun m -> m "[EXT] ListExt.type_check_expr: List.%a; args= %a; expected_is_ghost=%b" Ident.pr c (Util.Print.pr_list_comma Expr.pr) expr_list (Type.is_ghost expected_typ));

      let expr_list = List.map expr_list ~f:(fun expr ->
        let ghost_status = Type.is_ghost expected_typ || (Type.is_ghost (Expr.to_type expr)) in

        Expr.set_type expr ((Expr.to_type expr) |> Type.set_ghost ghost_status)
      )
      in

      let* expr_list = Rewriter.List.map  expr_list ~f:(fun expr -> type_check_expr_functs.process_expr expr (Expr.to_type expr)) in

      let is_ghost = List.fold ~init:false (expected_typ :: List.map exprs ~f:Expr.to_type) 
        ~f:(fun accum tp -> 
        accum || Type.is_ghost tp 
      )
      in

      match c, exprs with
      | ident, [ls_head; ls_tail] when Ident.(ident = cons_ident)  ->
        let expected_typ = expected_typ |> Type.set_ghost is_ghost in
        let elem_type = match expected_typ with
          | App (TypeExt ListConstr, [elem_typ], _) -> (elem_typ |> Type.set_ghost_to expected_typ)
          | App (Any, [], _) -> Type.any |> Type.set_ghost_to expected_typ
          | _typ -> 
              type_check_expr_functs.type_mismatch_error expr_attr.expr_loc (Type.App (TypeExt ListConstr, [Type.any], Type.mk_attr (expr_attr.expr_loc)))  _typ
        in
        (* Logs.debug (fun m -> m "[EXT] ListExt.type_check_expr: elem_typ=%a; is_ghost=%b; ls_head = %a" Type.pr elem_type (Type.is_ghost elem_type) Expr.pr ls_head); *)
        let* ls_head = type_check_expr_functs.process_expr ls_head elem_type in 
        let elem_type = (Expr.to_type ls_head) in

        let list_type = (Type.App (TypeExt ListConstr, [elem_type], Type.mk_attr (expr_attr.expr_loc))) |> Type.set_ghost_to expected_typ in

        let* ls_tail = type_check_expr_functs.process_expr ls_tail list_type in
        let list_type = list_type |> Type.set_ghost (Type.is_ghost (Expr.to_type ls_head) || Type.is_ghost (Expr.to_type ls_tail)) in

        type_check_expr_functs.check_and_set
        (App (ExprExt (ListExpr cons_ident), [ls_head; ls_tail], expr_attr)) list_type list_type list_type

      | ident, _ when Ident.(c = cons_ident)  ->
        Error.type_error expr_attr.expr_loc "Incorrect number of arguments for List Cons expression"

      | ident, [] when Ident.(ident = nil_ident) ->
        Logs.debug (fun m -> m "[Ext] ListExt.type_check_expr: typechecking nil");

        let elem_type = match expected_typ with
        | App (TypeExt ListConstr, [elem_typ], _) -> elem_typ |> Type.set_ghost is_ghost
        | App (Any, [], _) -> Type.bot
        | _typ -> type_check_expr_functs.type_mismatch_error expr_attr.expr_loc (Type.App (TypeExt ListConstr, [Type.any], Type.mk_attr (expr_attr.expr_loc)))  _typ
        in

        let list_type = (Type.App (TypeExt ListConstr, [elem_type], Type.mk_attr (expr_attr.expr_loc))) in
        
        type_check_expr_functs.check_and_set
        (App (ExprExt (ListExpr nil_ident), [], expr_attr)) list_type list_type list_type

      | ident, _ when Ident.(ident = nil_ident) ->
        Error.type_error expr_attr.expr_loc "Incorrect number of arguments for List.nil expression"

      | ident, [] ->
        Error.internal_error expr_attr.expr_loc ("[EXT] ListExt.type_check_expr: Unknown list function called: " ^ (Ident.to_string ident))

      | ident, ls_expr :: args ->
        let* lib_list_module = Rewriter.find_and_reify_module Predefs.lib_list_mod_qual_ident in
        
        let does_elem_exist = List.find lib_list_module.mod_def ~f:(fun mem -> 
          match mem with 
          | Import _ -> false 
          | SymbolDef symbol -> Ident.(Symbol.to_name symbol = ident) 
        ) in
      
        match does_elem_exist with
        (* callable does not exist inside Library.ListM *)
        | None | Some Import _->
          Error.internal_error expr_attr.expr_loc ("[EXT] ListExt: Unknown list function called: " ^ (Ident.to_string ident))

        (* found callable inside Library.ListM *)
        | Some SymbolDef symbol ->
          let* ls_expr = type_check_expr_functs.process_expr ls_expr (Type.any |> Type.set_ghost is_ghost) in

          let elem_type = match (Expr.to_type ls_expr) with
          | App (TypeExt ListConstr, [elem_typ], _) -> 
              elem_typ |> Type.set_ghost (is_ghost || Type.is_ghost elem_typ)
          | _tp -> 
            let list_type = (Type.App (TypeExt ListConstr, [Type.any], Type.mk_attr (expr_attr.expr_loc))) in
            type_check_expr_functs.type_mismatch_error expr_attr.expr_loc list_type _tp
          in

          let is_ghost = is_ghost || Type.is_ghost elem_type in

          let list_type = (Type.App (TypeExt ListConstr, [elem_type], Type.mk_attr (expr_attr.expr_loc))) |> Type.set_ghost is_ghost in

          let* args = Rewriter.List.map args ~f:(fun arg -> 
            type_check_expr_functs.process_expr arg 
              (Type.any |> Type.set_ghost is_ghost)
          ) in

          if Ident.(ident = len_ident) then
            let expected_typ = Type.int |> Type.set_ghost is_ghost in
            match args with
            | [] -> type_check_expr_functs.check_and_set (Expr.App (ExprExt (ListExpr ident), [ls_expr], expr_attr)) expected_typ expected_typ expected_typ
            | _ -> Error.type_error expr_attr.expr_loc "[EXT] ListExt: List.len called with incorrect number of arguments"
          else if Ident.(ident = is_in_ident) then
            let expected_typ = Type.bool |> Type.set_ghost is_ghost in
            match args with
            | [elem_arg] ->
              if Type.(elem_type = Expr.to_type elem_arg) then
                type_check_expr_functs.check_and_set (Expr.App (ExprExt (ListExpr ident), ls_expr :: args, expr_attr)) expected_typ expected_typ expected_typ
              else 
                type_check_expr_functs.type_mismatch_error (Expr.to_loc elem_arg) elem_type (Expr.to_type elem_arg)
            | _ -> Error.type_error expr_attr.expr_loc "[EXT] ListExt: List.is_in called with incorrect number of arguments"
          else if Ident.(ident = hd_destr_ident) then
            match args with
            | [] -> 
              type_check_expr_functs.check_and_set (Expr.App (ExprExt (ListExpr ident), [ls_expr], expr_attr)) elem_type elem_type elem_type

            | _ -> Error.type_error expr_attr.expr_loc "[EXT] ListExt: List.hd called with incorrect number of arguments"
          else if Ident.(ident = tl_destr_ident) then
            match args with 
            | [] ->
              type_check_expr_functs.check_and_set (Expr.App (ExprExt (ListExpr ident), [ls_expr], expr_attr)) list_type list_type list_type
            | _ -> Error.type_error expr_attr.expr_loc "[EXT] List.tl called with incorrect number of arguments"
          else
            Error.internal_error expr_attr.expr_loc ("[EXT] ListExt.type_check_expr: Unknown list function called: " ^ (Ident.to_string ident))
      end

    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ type_check_expr_functs

  let type_check_stmt = Cont.type_check_stmt

  (* Rewrites *)
  let rewrite_type_ext (type_ext: Type.type_ext) (tp_list: type_expr list) (loc: location) =
    let open Rewriter.Syntax in
    match type_ext, tp_list with
    | ListConstr, [elem_typ] -> 
      
      let* list_module_insert_scope, list_module_reference_scope =
        (* In case of elem_typ being in an instantiated module, like so:
          `module M = N[P]; type T' = List[M.T]` 
        we need to insert the elem_typ Type Module in the original interface `N`, and refer to it using `M` *)
      
        let largest_prefix = ProgUtils.largest_common_prefix_qi (Type.symbols elem_typ) in
        let+ result = Rewriter.resolve_and_find_opt largest_prefix in
        match result with
        | None -> 
          Error.internal_error Loc.dummy "[EXT] ListExt: rewrite_type_ext: largest_prefix scope not found"
        | Some (qi, (name, symbol, (b, subst_map))) ->

          name, qi
      in

      Logs.debug (fun m -> m "[EXT] ListExt.rewriter_type_ext: Elem_typ=%a; list_module_insert_scope=%a; list_module_reference_scope=%a" Type.pr elem_typ QualIdent.pr list_module_insert_scope QualIdent.pr list_module_reference_scope);

      let* type_module_qi = 
        let type_module_canonical_qi = 
          let mod_name_string = ProgUtils.tp_mod_ident_prefix ^ Type.to_string elem_typ in
          let type_module_ident = Ident.make loc (ProgUtils.serialize mod_name_string) 0 in
          QualIdent.append list_module_reference_scope type_module_ident
        in

        let* resolve_result = 
          Rewriter.resolve_opt type_module_canonical_qi in
        
        match resolve_result with
        | Some _ -> Rewriter.return type_module_canonical_qi
        | None ->
          let+ _ = 
            ProgUtils.intros_type_module ~loc ~scope:list_module_insert_scope ~f:!(Rewriter.process_symbol_ref) elem_typ in
          type_module_canonical_qi
      in 

      Logs.debug (fun m -> m "[EXT] ListExt.rewriter_type_ext: type_module_qi=%a" QualIdent.pr type_module_qi);

      let list_module_ident = 
        let mod_name_string = ListPredefs.list_mod_ident_prefix ^ Type.to_string elem_typ in
        Ident.make loc (ProgUtils.serialize mod_name_string) 0
      in

      let list_module_inst = Module.ModInst {
            mod_inst_name = list_module_ident;
            mod_inst_type = Predefs.lib_list_mod_qual_ident;
            mod_inst_def = Some (Predefs.lib_list_mod_qual_ident, [type_module_qi]);
            mod_inst_is_interface = false;
            mod_inst_loc = loc;
      } in

      let* list_module_inst_qi = 
        let module_qi = QualIdent.append list_module_reference_scope list_module_ident in

        let* resolve_result = Rewriter.resolve_opt module_qi in
        match resolve_result with
          | Some _ -> 
            Rewriter.return module_qi
          | None ->
            let+ _ = 
            Rewriter.introduce_typecheck_symbol_at_scope' ~loc list_module_inst list_module_insert_scope in
            module_qi
      in

      Logs.debug (fun m -> m "[EXT] ListExt.rewriter_type_ext: list_module_inst_qi=%a" QualIdent.pr list_module_inst_qi);

      Rewriter.return (Type.mk_var ~loc (QualIdent.append list_module_inst_qi Predefs.lib_type_rep_type_ident))

    | ListConstr, _ ->
      Error.type_error loc "[EXT] ListExt: List type used with unexpected number of arguments"

    | _ -> Cont.rewrite_type_ext type_ext tp_list loc

  let rewrite_expr_ext (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr: Expr.expr_attr) = 
    (* let open Rewriter.Syntax in *)
    let loc = expr_attr.expr_loc in

    match expr_ext, expr_list with
    | ListExpr ident, [hd; tail] when Ident.(ident = cons_ident) ->
      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: List.cons");
      let module_name = begin match expr_attr.expr_type with
      | Type.App (Var tp_qid, [], _) ->
        QualIdent.pop tp_qid
      | _ ->
        Error.internal_error loc "[EXT] ListExt.rewrite_expr_ext crashed1; expected List Module name type"
      end 
      in

      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: expr_typ = %a" Type.pr expr_attr.expr_type);

      let constr_qid = QualIdent.append module_name Predefs.lib_list_cons_ident in

      
      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: constr_qid = %a" QualIdent.pr constr_qid);
      
      Expr.mk_app ~loc ~typ:expr_attr.expr_type (DataConstr constr_qid) [hd; tail] |> Rewriter.return

    | ListExpr ident, [] when Ident.(ident = nil_ident)  ->
      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: List.nil");
      let module_name = begin match expr_attr.expr_type with
      | Type.App (Var tp_qid, [], _) ->
        QualIdent.pop tp_qid
      | _tp ->
        Error.internal_error loc ("[EXT] ListExt.rewrite_expr_ext crashed2; expected List Module name type; got " ^ (Type.to_string _tp))
      end 
      in

      let constr_qid = QualIdent.append module_name Predefs.lib_list_nil_ident in
      
      Expr.mk_app ~loc ~typ:expr_attr.expr_type (DataConstr constr_qid) [] |> Rewriter.return
    
    | ListExpr ident, [ls_arg] when Ident.(ident = hd_destr_ident) ->
      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: List.hd");
      let module_name = begin match Expr.to_type ls_arg with
      | Type.App (Var tp_qid, [], _) ->
        QualIdent.pop tp_qid
      | _ ->
        Error.internal_error loc "[EXT] ListExt.rewrite_expr_ext crashed3; expected List Module name type"
      end 
      in

      let constr_qid = QualIdent.append module_name Predefs.lib_list_head_destr_ident in
      
      Expr.mk_app ~loc ~typ:expr_attr.expr_type (DataDestr constr_qid) [ls_arg] |> Rewriter.return

    | ListExpr ident, [ls_arg] when Ident.(ident = tl_destr_ident) ->
      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: List.tl");
      let module_name = begin match Expr.to_type ls_arg with
      | Type.App (Var tp_qid, [], _) ->
        QualIdent.pop tp_qid
      | _ ->
        Error.internal_error loc "[EXT] ListExt.rewrite_expr_ext crashed4; expected List Module name type"
      end 
      in

      let constr_qid = QualIdent.append module_name Predefs.lib_list_tail_destr_ident in
      
      Expr.mk_app ~loc ~typ:expr_attr.expr_type (DataDestr constr_qid) [ls_arg] |> Rewriter.return

    | ListExpr ident, ls_arg :: args ->
      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: %a" Ident.pr ident);
      
      let module_name = begin match (Expr.to_type ls_arg) with
      | Type.App (Var tp_qid, [], _) ->
        QualIdent.pop tp_qid
      | _ ->
        Logs.debug (fun m -> m "expr_type: %a" Type.pr expr_attr.expr_type);
        Error.internal_error loc "[EXT] ListExt.rewrite_expr_ext crashed; expected List Module name type"
      end
      in

      let call_qid = QualIdent.append module_name ident in
      
      Expr.mk_app ~loc ~typ:expr_attr.expr_type (Var call_qid) (ls_arg :: args) |> Rewriter.return
    
    
    | ListExpr ident, [] ->
      Error.type_error loc "[EXT] ListExt.rewrite_expr_ext: Unknown ident." 

    | _ -> Cont.rewrite_expr_ext expr_ext expr_list expr_attr

  let rewrite_stmt_ext = Cont.rewrite_stmt_ext


  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
  let ext_local_vars = local_vars @ Cont.ext_local_vars
end
