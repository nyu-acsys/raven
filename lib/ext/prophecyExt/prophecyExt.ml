open Base
open Ast
open ExtApi
open Util

(* module ListExt = ListExt.ListExt(DefaultExt.DefaultExt) *)

module ProphecyExt (Cont : ListApi.ListApi) = struct
  let lib_source = Some ("prophecyLib.rav", [%blob "prophecyLib.rav"])
  let local_vars = []

  module ProphPredefs = struct
    let proph_mod_ident = Ident.make Loc.dummy "Prophecy" 0
    let proph_mod_qi = QualIdent.from_list [Predefs.lib_ident; proph_mod_ident]
    let field_ident = Ident.make Loc.dummy "prophecyValue" 0

    let proph_mod_ident_prefix = "ProphecyMod$" 
  end

  type Type.type_ext +=
    | ProphId

  type Expr.expr_ext +=
    | ProphResource

  type Stmt.stmt_ext +=
    | NewProph of bool * type_expr
    | ResolveProph

  let proph_id_type ~loc = Type.mk_app ~loc ~ghost:true (TypeExt ProphId) []


  (* AstDef *)
  let type_ext_to_name type_ext = match type_ext with
  | ProphId -> "ProphId"
  | _x -> 
    (* let ext_string = (Stdlib.Obj.Extension_constructor.name 
    (Stdlib.Obj.Extension_constructor.of_val (Stdlib.Obj.repr _x))) in *)
    (* Logs.debug (fun m -> m "[EXT] ProphecyExt: %s" 
    ext_string); *)

    Cont.type_ext_to_name type_ext

  let expr_ext_to_string expr_ext =
    match expr_ext with 
    | ProphResource -> "Prophecy"
    | _ -> Cont.expr_ext_to_string expr_ext

  let pr_stmt_ext ppf ext expr_list = 
    let open Stdlib.Format in
    match ext, expr_list with
    | (NewProph (b, typ)), [proph_id; proph_val] ->
      fprintf ppf "@[[EXT] %a, %a@ :=@ NewProph(oneshot:%b, typ:%a)@]" Expr.pr proph_id Expr.pr proph_val b Type.pr typ

    | NewProph _, _ ->
      Error.internal_error Loc.dummy "[EXT] ProphecyExt.pr_stmt_ext: wrong number of arguments called for NewProph"
    
    | ResolveProph, [proph_id; resolve_val] ->
      fprintf ppf "@[[EXT] ResolveProph(%a -> %a)@]" Expr.pr proph_id Expr.pr resolve_val 

    | ResolveProph, _ ->
      Error.internal_error Loc.dummy "[EXT] ProphecyExt.pr_stmt_ext: wrong number of arguments called for ResolveProph"

    | _ -> Cont.pr_stmt_ext ppf ext expr_list

  let stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | NewProph _ -> Set.empty (module QualIdent)
    | ResolveProph -> Set.empty (module QualIdent)
    | _ -> Cont.stmt_ext_symbols stmt_ext

  let stmt_ext_local_vars_modified stmt_ext exprs =
    match stmt_ext, exprs with
    | NewProph _, [proph_id; proph_val] ->
      if Expr.is_ident proph_val then
        [Expr.to_ident proph_id; Expr.to_ident proph_val]
      else
          [Expr.to_ident proph_id]

    | NewProph _, _ ->
      Error.internal_error Loc.dummy "[EXT] ProphecyExt: wrong number of arguments called for NewProph"

    | ResolveProph, [proph_id; resolve_val] ->
      [Expr.to_ident proph_id]

    | ResolveProph, _ ->
      Error.internal_error Loc.dummy "[EXT] ProphecyExt: wrong number of arguments called for ResolveProph"

    | _ -> Cont.stmt_ext_local_vars_modified stmt_ext exprs

  let prophecy_module_ident ~loc typ = 
      let prophecy_mod_string = ProphPredefs.proph_mod_ident_prefix ^ Type.to_string typ in
      Ident.make loc (ProgUtils.serialize prophecy_mod_string) 0

  let prophecy_module_from_type_qi ~loc typ =
    let symbols = Type.symbols typ in
    let module_scope = ProgUtils.largest_common_prefix_qi symbols in

    QualIdent.append module_scope (prophecy_module_ident ~loc typ)

  let stmt_ext_fields_accessed stmt_ext exprs = 
    match stmt_ext, exprs with
    | NewProph (_, typ), _ ->
      let proph_mod_qi = prophecy_module_from_type_qi ~loc:Loc.dummy typ in
      let proph_field_ident = ProphPredefs.field_ident in

      [QualIdent.append proph_mod_qi proph_field_ident]

    | ResolveProph, [proph_id; resolve_val] ->
      let typ = Expr.to_type resolve_val in
      let proph_mod_qi = prophecy_module_from_type_qi ~loc:Loc.dummy typ in
      let proph_field_ident = ProphPredefs.field_ident in

      [QualIdent.append proph_mod_qi proph_field_ident]

    | ResolveProph, _ ->
      Error.internal_error Loc.dummy "[EXT] ProphecyExt: wrong number of arguments called for ResolveProph"

    | _ -> Cont.stmt_ext_fields_accessed stmt_ext exprs


  (* Rewriter *)
  let expr_ext_rewrite_types = Cont.expr_ext_rewrite_types
  let stmt_ext_rewrite_types ~f stmt_ext = 
    let open Rewriter.Syntax in
    match stmt_ext with
    | NewProph (b, tp_expr) ->
      let+ tp_expr = f tp_expr in
      NewProph (b, tp_expr)
    |_ -> Cont.stmt_ext_rewrite_types ~f stmt_ext


  (* Typing *)
  let type_check_type_expr type_ext type_args type_attr type_check_type_expr_functs = 
    match type_ext, type_args with
    | ProphId, [] ->
      Rewriter.return @@  (Type.App (TypeExt ProphId, [], type_attr) |> Type.set_ghost true)
      
    | ProphId, _ ->
      Error.type_error type_attr.Type.type_loc "[EXT] ProphecyExt: wrong number of arguments used with ProphId type"

    | _ -> Cont.type_check_type_expr type_ext type_args type_attr type_check_type_expr_functs

  let type_check_expr (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr : Expr.expr_attr) (expected_typ: type_expr) (type_check_expr_functs: type_check_expr_functs) = 
    let open Rewriter.Syntax in
    let loc = expr_attr.expr_loc in

    match expr_ext, expr_list with
    | ProphResource, [proph_id_expr; value_expr] ->
      let proph_id_type = proph_id_type ~loc:expr_attr.expr_loc in
      let* proph_id_expr = type_check_expr_functs.process_expr proph_id_expr proph_id_type in
      let* value_expr = type_check_expr_functs.process_expr
      value_expr (Type.any |> Type.set_ghost true) in

      let elem_tp_opt = Cont.list_tp_to_elem_typ (Expr.to_type value_expr) in

      begin match elem_tp_opt with
      | None -> Error.type_error loc 
          ("[EXT] ProphecyExt: prophecy() expected to be called with List types; found: " ^ (Type.to_string (Expr.to_type value_expr)))
      | Some _elem_typ ->
        Rewriter.return @@ (Expr.mk_app ~loc ~typ:Type.perm (ExprExt ProphResource) [proph_id_expr; value_expr]) 
      end
    
    | ProphResource, _ ->
      Error.type_error loc "[EXT] ProphecyExt: prophecy() called with incorrect number of arguments"

    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ type_check_expr_functs

  let type_check_stmt call_decl (stmt_ext : Stmt.stmt_ext) (expr_list: expr list) (stmt_loc: Loc.t) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : ExtApi.type_check_stmt_functs)
  :
      (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t = 

    Logs.debug (fun m -> m "[EXT] ProphecyExt.type_check_stmt: started");
    
    let open Rewriter.Syntax in
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    match stmt_ext, expr_list with
    | NewProph (oneshot_b, typ), [proph_id; proph_val] ->
      let* proph_id = type_check_stmt_functs.disambiguate_process_expr proph_id (proph_id_type ~loc:stmt_loc) disam_tbl
      
      in

      let proph_val_typ = if oneshot_b then
        typ |> Type.set_ghost true
      else
        Cont.mk_list_tp stmt_loc typ |> Type.set_ghost true
      in

      begin match Expr.is_ident proph_val with
      | false ->
        Error.type_error stmt_loc "[EXT] ProphecyExt: NewProph should only be called with a local variable for value."
      
      | true ->
        let* proph_val = type_check_stmt_functs.disambiguate_process_expr proph_val proph_val_typ disam_tbl in

        (Stmt.StmtExt (
          NewProph (oneshot_b, typ), [proph_id; proph_val]
        ), disam_tbl) |> Rewriter.return
      end
    | NewProph _, _ ->
      Error.type_error stmt_loc "[EXT] ProphecyExt: NewProph called with incorrect number of arguments"

    | ResolveProph, [proph_id; resolve_value] ->
      let* proph_id = type_check_stmt_functs.disambiguate_process_expr proph_id (proph_id_type ~loc:stmt_loc) disam_tbl in

      let* resolve_value = type_check_stmt_functs.disambiguate_process_expr resolve_value (Type.any |> Type.set_ghost true) disam_tbl in

      (Stmt.StmtExt (
        ResolveProph, [proph_id; resolve_value]
      ), disam_tbl) |> Rewriter.return

    | ResolveProph, _ ->
      Error.type_error stmt_loc "[EXT] ProphecyExt: ResolveProph called with incorrect number of arguments"

    | _ -> Cont.type_check_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl type_check_stmt_functs


  (* Rewrites *)

  (** Safely initialize prophecy module and return its qual_ident. In particular, this function is idempotent, so can be called whenever need to convert a type_expr into its corresponding prophecy_module_qual_ident. *)
  let initialize_prophecy_module loc (typ: type_expr): qual_ident Rewriter.t =
    let open Rewriter.Syntax in
    
    let proph_module_qi = prophecy_module_from_type_qi ~loc typ 
    in

    Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Looking up proph_module_qi: %a" QualIdent.pr proph_module_qi);
    let* lookup = Rewriter.resolve_and_find_opt proph_module_qi in

    match lookup with
    | Some _ ->
      Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Look-up succeeded for proph_module_qi: %a" QualIdent.pr proph_module_qi);
      Rewriter.return proph_module_qi

    | None -> 
      Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Proph module not found. Initializing... proph_module_qi: %a" QualIdent.pr proph_module_qi);
      (* Proph Module not found. Initializing... *)
      let* proph_module_insert_scope, proph_module_reference_scope = 
        let largest_prefix = QualIdent.pop proph_module_qi in

        let* result = Rewriter.resolve_and_find_opt largest_prefix in
        begin match result with
        | None ->
          Error.internal_error loc "[EXT ProphecyExt: largest_prefix scope not found"
        | Some (qi, (name, symbol, (b, subst_map))) ->
          Rewriter.return (name, qi)
        end
      in

      let* type_module_qi = 
        (* Module must be of List[typ] *)
        let list_typ = Cont.mk_list_tp loc typ in

        let type_module_canonical_qi =
          let mod_name_string = ProgUtils.tp_mod_ident_prefix ^ Type.to_string list_typ in
          let type_module_ident = Ident.make loc (ProgUtils.serialize mod_name_string) 0 in
          QualIdent.append proph_module_reference_scope type_module_ident
        in

        let* resolve_result = Rewriter.resolve_opt type_module_canonical_qi in

        match resolve_result with
        | Some _ -> 
          Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Type Module found. type_module_qi: %a" QualIdent.pr type_module_canonical_qi);
          Rewriter.return type_module_canonical_qi
        | None ->
          Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Type module also not found. Initializing... type_module_qi: %a" QualIdent.pr type_module_canonical_qi);
            let+ introd_type_module_qi = 
              ProgUtils.intros_type_module ~loc ~scope:proph_module_insert_scope ~f:!(Rewriter.process_symbol_ref) list_typ in
          
          Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Type module successfully initialized. type_module_qi: %a" QualIdent.pr type_module_canonical_qi);
            type_module_canonical_qi
      in

      let proph_module_ident = prophecy_module_ident ~loc typ in

      let proph_module_inst = Module.ModInst {
        mod_inst_name = proph_module_ident;
        mod_inst_type = ProphPredefs.proph_mod_qi;
        mod_inst_def = Some (ProphPredefs.proph_mod_qi, [type_module_qi]);
        mod_inst_is_interface = false;
        mod_inst_loc = loc;
      } in

      Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: proph_module_ident = %a; about to introduce" Ident.pr proph_module_ident);

      let* _proph_module_inst_qi = 
        Rewriter.introduce_typecheck_symbol_at_scope' ~loc proph_module_inst proph_module_insert_scope in

      Rewriter.return proph_module_qi
  
  let rewrite_type_ext (type_ext: Type.type_ext) (tp_list: type_expr list) (loc: location) : type_expr Rewriter.t =
    match type_ext, tp_list with
    | ProphId, [] ->
      Rewriter.return Type.ref
    | ProphId, _ ->
      Error.type_error loc "[EXT] ProphExt: ProphId type constructor used with incorrect number of arguments"
    | _ -> Cont.rewrite_type_ext type_ext tp_list loc

  let rewrite_expr_ext (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr: Expr.expr_attr) = 
    let open Rewriter.Syntax in
    let loc = expr_attr.expr_loc in
    match expr_ext, expr_list with
    | ProphResource, [proph_id; value] ->
      let* proph_type = 
        let elem_tp_opt = Cont.list_tp_to_elem_typ (Expr.to_type value) in

        match elem_tp_opt with
        | None -> Error.type_error loc ("[EXT] ProphecyExt: Prophecy resources must hold List values; found: " ^ (Type.to_string (Expr.to_type value)))
        | Some elem_typ -> 
          let+ elem_typ = !Rewriter.expand_type_expr_ref elem_typ in
          elem_typ
      in

      let* proph_module_qi = initialize_prophecy_module loc proph_type in
      let prophecy_field_qi = QualIdent.append proph_module_qi ProphPredefs.field_ident in

      let* prophecy_field = Rewriter.find_and_reify_field prophecy_field_qi in

      Expr.mk_app ~typ:Type.perm ~loc Own [
        proph_id; 
        Expr.mk_var ~typ:prophecy_field.field_type prophecy_field_qi;
        value;
        Expr.mk_real ~loc 1.0;
      ] |> Rewriter.return

    | _ -> Cont.rewrite_expr_ext expr_ext expr_list expr_attr

  let rewrite_stmt_ext (stmt_ext: Stmt.stmt_ext) (expr_list: expr list) loc: Stmt.t Rewriter.t =
    let open Rewriter.Syntax in

    Logs.debug (fun m -> m "[EXT] ProphecyExt.rewrite_stmt: Starting");

    match stmt_ext, expr_list with
    | NewProph (oneshot_b, typ), [proph_id; proph_val] ->

      Logs.debug (fun m -> m "[EXT] ProphecyExt.rewrite_stmt: NewProph(one_shot:%b; type:%a)" oneshot_b Type.pr typ);

      let* proph_module_qi = initialize_prophecy_module loc typ in
      let prophecy_field_qi = QualIdent.append proph_module_qi ProphPredefs.field_ident in

      let* prophecy_field_symbol = Rewriter.find_and_reify_field prophecy_field_qi in

      let havoc_stmt1 = Stmt.mk_havoc ~loc (Expr.to_qual_ident proph_id) in
      let havoc_stmt2 = Stmt.mk_havoc ~loc (Expr.to_qual_ident proph_val) in

      let* proph_field_val = if not oneshot_b then 
        Rewriter.return proph_val 
      else
          (* For one-shot prophecies, generating an arbitrary tail of predictions. *)
        let tl_var = Type.mk_var_decl ~const:true ~ghost:true (Ident.fresh loc "$proph_oneshot_trail") (Cont.mk_list_tp loc (Expr.to_type proph_val)) in
        let+ tl_var_qi = Rewriter.introduce_typecheck_symbol' ~loc (
          VarDef { 
            var_decl=tl_var;
            var_init=None
          }
        ) in

        Cont.ls_cons loc (proph_val) (Expr.from_var_decl tl_var)
      in

      let proph_new_stmt =
        Stmt.mk_inhale_expr ~loc
        ~cmnt:("[EXT] ProphExt: Inhale stmt for Prophecy.new()")
        (Expr.mk_app ~loc ~typ:Type.perm Expr.Own [
          proph_id; 
          Expr.mk_var ~typ:prophecy_field_symbol.field_type prophecy_field_qi; 
          proph_field_val;
          Expr.mk_real 1.0;
        ])
        (* let new_desc = {
          Stmt.new_lhs = Expr.to_qual_ident proph_id;
          new_args = [(prophecy_field_qi, Some proph_field_val)]
          } in

        { Stmt.stmt_desc = Basic (New new_desc); stmt_loc = loc } *)
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc ~ghost:true
        [havoc_stmt1; havoc_stmt2; proph_new_stmt]
      )

    | NewProph _, _ ->
            Error.type_error loc "[EXT] ProphExt: NewProph command called with incorrect number of arguments"

    | ResolveProph, [proph_id; resolve_value] ->
      let* proph_module_qi = initialize_prophecy_module loc (Expr.to_type resolve_value) in
      let prophecy_field_qi = QualIdent.append proph_module_qi 
        (Ident.set_loc loc ProphPredefs.field_ident) 
      in

      let* prophecy_field = Rewriter.find_and_reify_field prophecy_field_qi in

      let proph_list_tp = Cont.mk_list_tp loc (Expr.to_type resolve_value) in

      let proph_read_var_def, proph_read_var_ident = 
        let proph_read_var_ident = Ident.fresh loc "$proph_read" in
        let proph_read_type = proph_list_tp in

        Stmt.{ 
          var_decl = Type.mk_var_decl ~ghost:true proph_read_var_ident ~loc proph_read_type ; 
          var_init = None;
        }, proph_read_var_ident
      in

      let* proph_id_var_def = Rewriter.find_and_reify_var (Expr.to_qual_ident proph_id) in

      let* _ = Rewriter.introduce_symbol (VarDef proph_read_var_def) in

      let field_read_stmt = 
        let field_read_desc = Stmt.{
          field_read_lhs=QualIdent.from_ident proph_read_var_ident;
          field_read_field=prophecy_field_qi;
          field_read_ref= Expr.set_loc (Expr.from_var_decl proph_id_var_def.var_decl) loc;
          field_read_is_init=true;
        } in

        Stmt.{stmt_desc = Basic (FieldRead field_read_desc); stmt_loc = loc; }
      in

      let prophetic_assertion = 
        Stmt.mk_assume_expr ~loc
        ~cmnt:("[EXT] ProphecyExt: Prophecising Assertion")
        (Expr.mk_eq 
          resolve_value
          (Cont.ls_hd loc (Expr.from_var_decl proph_read_var_def.var_decl))
          )
      in

      let list_non_empty =
        Stmt.mk_assume_expr ~loc
        ~cmnt:("[EXT] ProphecyExt: Assuming remaining prophecy stream non-empty")
        (Expr.mk_app ~loc ~typ:Type.bool Gt 
          [(Cont.ls_len loc (Expr.from_var_decl proph_read_var_def.var_decl)); 
          Expr.mk_int 2]
        )
      in

      let field_write_val = 
        Cont.ls_tl loc (Expr.from_var_decl proph_read_var_def.var_decl)
      in

      let field_write_stmt = 
        let field_write_desc = Stmt.{
          field_write_ref = Expr.from_var_decl proph_id_var_def.var_decl;
          field_write_field = prophecy_field_qi;
          field_write_val = field_write_val
        } in

        Stmt.{stmt_desc = Basic (FieldWrite field_write_desc); stmt_loc = loc;}
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc ~ghost:true
        [field_read_stmt; prophetic_assertion; list_non_empty; field_write_stmt])

    | ResolveProph, _ ->
      Error.type_error loc "[EXT] ProphExt: ResolveProph command called with incorrect number of arguments"

    | _ -> Cont.rewrite_stmt_ext stmt_ext expr_list loc


  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
  let ext_local_vars = local_vars @ Cont.ext_local_vars
end