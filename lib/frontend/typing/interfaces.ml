(** Checks that a module conforms to the interfaces it implements. *)

open Base
open Ast
open Util
open TypingMonad

(* [manifest_subst] maps a manifest field's name in the interface's specs (`Impl.f`) to
   the field it stands for (`g`), so that specs naming either compare equal. *)
let check_implements_symbol ?(manifest_subst = Map.empty (module QualIdent))
    interface_ident (symbol : Symbol.t) (orig_symbol : Symbol.t) : unit t =
  let open Rewriter.Syntax in
  let loc = Symbol.to_loc symbol in
  let ident = Symbol.to_name symbol in
  match (symbol, orig_symbol) with
  (* An inherited field may be redeclared only as a manifest field naming an existing
     field; a plain redeclaration would add a second field, which is rejected below. *)
  | FieldDef ({ field_alias = Some target; _ } as field_def), FieldDef orig_field_def ->
      let* target_type = TypeExpr.expand_type_expr field_def.field_type
      and* orig_type = TypeExpr.expand_type_expr orig_field_def.field_type in
      if not (Type.equal target_type orig_type) then
        Error.type_error loc
          (Printf.sprintf
             !"Field %{Ident} stands for %{QualIdent}, of type %{Type}, but interface \
               %{QualIdent} declares it with type %{Type}"
             ident target target_type interface_ident orig_type)
      else if Bool.(field_def.field_is_ghost <> orig_field_def.field_is_ghost) then
        Error.type_error loc
          (Printf.sprintf
             !"Field %{Ident} is declared %s, but interface %{QualIdent} declares it %s"
             ident
             (if field_def.field_is_ghost then "ghost" else "non-ghost")
             interface_ident
             (if orig_field_def.field_is_ghost then "ghost" else "non-ghost"))
      else Rewriter.return ()
  | TypeDef typ_def, TypeDef orig_typ_def -> (
      if Bool.(typ_def.type_def_rep <> orig_typ_def.type_def_rep) then
        Error.type_error loc
          (Printf.sprintf
             !"Cannot change rep type annotation for type %{Ident} inherited from \
               interface %{QualIdent}"
             ident interface_ident)
      else
        match (typ_def.type_def_expr, orig_typ_def.type_def_expr) with
        | None, Some _ ->
            Error.type_error loc
              (Printf.sprintf
                 !"Type %{Ident} cannot be redeclared as abstract. It was already \
                   defined in interface %{QualIdent}"
                 ident interface_ident)
        | Some _tp, Some _orig_tp ->
            Error.type_error loc
              (Printf.sprintf
                 !"Type %{Ident} was already defined in interface %{QualIdent}"
                 ident interface_ident)
        | _ -> Rewriter.return ())
  | VarDef var_def, VarDef orig_var_def -> (
      if var_def.var_decl.var_ghost && not orig_var_def.var_decl.var_ghost then
        Error.type_error loc
          (Printf.sprintf
             !"Cannot redeclare %s %{Ident} from interface %{QualIdent} as ghost"
             (Symbol.kind symbol) ident interface_ident)
      else if (not var_def.var_decl.var_ghost) && orig_var_def.var_decl.var_ghost then
        Error.type_error loc
          (Printf.sprintf
             !"Cannot redeclare ghost %s %{Ident} from interface %{QualIdent} as \
               non-ghost"
             (Symbol.kind symbol) ident interface_ident)
      else
        let* orig_var_def_var_type =
          TypeExpr.expand_type_expr orig_var_def.var_decl.var_type
        in

        if Type.(var_def.var_decl.var_type <> orig_var_def_var_type) then
          Error.type_error loc
            (Printf.sprintf
               !"%s %{Ident} must have type %{Type} according to interface %{QualIdent}"
               (Symbol.kind symbol |> String.capitalize)
               ident orig_var_def.var_decl.var_type interface_ident)
        else
          match (var_def.var_init, orig_var_def.var_init) with
          | _, Some _ ->
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} was already defined in interface %{QualIdent}. It \
                     cannot be redefined"
                   (Symbol.kind symbol |> String.capitalize)
                   ident interface_ident)
          | _ -> Rewriter.return ())
  | CallDef call_def, CallDef orig_call_def -> (
      let make_subst decls odecls sm =
        Rewriter.List.fold2 decls odecls ~init:sm
          ~f:(fun sm (var_decl : var_decl) (ovar_decl : var_decl) ->
            let+ ovar_decl_var_type = TypeExpr.expand_type_expr ovar_decl.var_type in
            if
              Bool.(var_decl.var_const <> ovar_decl.var_const)
              || Bool.(var_decl.var_implicit <> ovar_decl.var_implicit)
              || Bool.(var_decl.var_ghost <> ovar_decl.var_ghost)
              || Type.(var_decl.var_type <> ovar_decl_var_type)
            then
              Error.type_error loc
                (Printf.sprintf
                   !"Formal parameter %{Ident} of %s %{Ident} does not match parameter \
                     %{Ident} of %{Ident} in interface %{QualIdent}"
                   var_decl.var_name (Symbol.kind symbol) ident ovar_decl.var_name ident
                   interface_ident)
            else
              Map.add_exn sm
                ~key:(QualIdent.from_ident ovar_decl.var_name)
                ~data:(QualIdent.from_ident var_decl.var_name))
        |> fun ret_val ->
        match%bind ret_val with
        | Ok sm -> Rewriter.return sm
        | Unequal_lengths ->
            Error.type_error loc
              (Printf.sprintf
                 !"%s %{Ident} does not have the same number of parameters as %{Ident} \
                   in interface %{QualIdent}"
                 (Symbol.kind symbol) ident ident interface_ident)
      in

      if
        Poly.(call_def.call_decl.call_decl_kind <> orig_call_def.call_decl.call_decl_kind)
      then
        Error.type_error loc
          (Printf.sprintf
             !"Cannot redeclare %s %{Ident} from %{QualIdent} as %s"
             (Symbol.kind orig_symbol) ident interface_ident (Symbol.kind symbol))
      else
        let* sm =
          make_subst call_def.call_decl.call_decl_formals
            orig_call_def.call_decl.call_decl_formals manifest_subst
        in
        let pre_ok =
          List.for_all2 call_def.call_decl.call_decl_precond
            orig_call_def.call_decl.call_decl_precond ~f:(fun spec orig_spec ->
              Bool.(spec.spec_atomic = orig_spec.spec_atomic)
              && Expr.alpha_equal ~sm spec.spec_form orig_spec.spec_form)
          |> function
          | Ok res -> res
          | Unequal_lengths -> false
        in
        let _ =
          if not pre_ok then
            Error.type_error loc
              (Printf.sprintf
                 !"%s %{Ident} does not have the same precondition as %{Ident} in \
                   interface %{QualIdent}. Repeat its contract exactly, or omit it to \
                   inherit it"
                 (Symbol.kind symbol) ident ident interface_ident)
        in
        let* sm =
          make_subst call_def.call_decl.call_decl_returns
            orig_call_def.call_decl.call_decl_returns sm
        in
        let post_ok =
          List.for_all2 call_def.call_decl.call_decl_postcond
            orig_call_def.call_decl.call_decl_postcond ~f:(fun spec orig_spec ->
              let post_ok =
                Bool.(spec.spec_atomic = orig_spec.spec_atomic)
                && Expr.alpha_equal ~sm spec.spec_form orig_spec.spec_form
              in
              post_ok)
          |> function
          | Ok res -> res
          | Unequal_lengths -> false
        in
        let _ =
          if not post_ok then
            Error.type_error loc
              (Printf.sprintf
                 !"%s %{Ident} does not have the same postcondition as %{Ident} in \
                   interface %{QualIdent}. Repeat its contract exactly, or omit it to \
                   inherit it"
                 (Symbol.kind symbol) ident ident interface_ident)
        in
        let opens_ok =
          let entry_expr (qi, args) = Expr.mk_app ~typ:Type.bool (Var qi) args in
          match
            (call_def.call_decl.call_decl_opens, orig_call_def.call_decl.call_decl_opens)
          with
          | None, None -> true
          | Some mask, Some orig_mask -> (
              match
                List.for_all2 mask orig_mask ~f:(fun entry orig_entry ->
                    Expr.alpha_equal ~sm (entry_expr entry) (entry_expr orig_entry))
              with
              | Ok res -> res
              | Unequal_lengths -> false)
          | _ -> false
        in
        let _ =
          if not opens_ok then
            Error.type_error loc
              (Printf.sprintf
                 !"%s %{Ident} does not have the same opens clause as %{Ident} in \
                   interface %{QualIdent}. Repeat its contract exactly, or omit it to \
                   inherit it"
                 (Symbol.kind symbol) ident ident interface_ident)
        in
        match (call_def.call_def, orig_call_def.call_def) with
        | ProcDef { proc_body = Some _; _ }, ProcDef { proc_body = Some _; _ }
        | FuncDef { func_body = Some _; _ }, FuncDef { func_body = Some _; _ } ->
            Error.type_error loc
              (Printf.sprintf
                 !"%s %{Ident} was already defined in interface %{QualIdent}. It cannot \
                   be redefined"
                 (Symbol.kind symbol |> String.capitalize)
                 ident interface_ident)
        | ProcDef { proc_body = None; _ }, ProcDef { proc_body = Some _; _ }
        | FuncDef { func_body = None; _ }, FuncDef { func_body = Some _; _ } ->
            Error.type_error loc
              (Printf.sprintf
                 !"%s %{Ident} cannot be redeclared as abstract. It was already defined \
                   in interface %{QualIdent}"
                 (Symbol.kind symbol |> String.capitalize)
                 ident interface_ident)
        | _ -> Rewriter.return ())
  | ModDef mod_def, ModInst orig_mod_inst -> (
      if mod_def.mod_decl.mod_decl_is_interface && not orig_mod_inst.mod_inst_is_interface
      then
        Error.type_error loc
          (Printf.sprintf
             !"Cannot redeclare module %{Ident} from interface %{QualIdent} as interface"
             ident interface_ident)
      else if
        (not mod_def.mod_decl.mod_decl_is_interface)
        && orig_mod_inst.mod_inst_is_interface
      then
        Error.type_error loc
          (Printf.sprintf
             !"Cannot redeclare interface %{Ident} from interface %{QualIdent} as module"
             ident interface_ident)
      else
        let _ =
          (* The module meets the interface's requirement if any of its parents is the
             required interface. *)
          let orig_mod_typ = orig_mod_inst.mod_inst_type in
          let implements_required =
            List.exists mod_def.mod_decl.mod_decl_returns ~f:(fun (mod_typ, _) ->
                QualIdent.equal mod_typ orig_mod_typ)
          in
          if not implements_required then
            Error.type_error loc
              (Printf.sprintf
                 !"%s %{Ident} must implement interface %{QualIdent} according to \
                   interface %{QualIdent}"
                 (Symbol.kind symbol |> String.capitalize)
                 ident orig_mod_typ interface_ident)
        in
        if not @@ List.is_empty mod_def.mod_decl.mod_decl_formals then
          Error.type_error loc
            (Printf.sprintf
               !"%s %{Ident} cannot have module parameters"
               (Symbol.kind symbol |> String.capitalize)
               ident)
        else
          match orig_mod_inst.mod_inst_def with
          | Some _ ->
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} was already defined in interface %{QualIdent}. It \
                     cannot be redefined"
                   (Symbol.kind symbol |> String.capitalize)
                   ident interface_ident)
          | _ -> Rewriter.return ())
  | ModInst mod_inst, ModInst orig_mod_inst -> (
      if mod_inst.mod_inst_is_interface && not orig_mod_inst.mod_inst_is_interface then
        Error.type_error loc
          (Printf.sprintf
             !"Cannot redeclare module %{Ident} from interface %{QualIdent} as interface"
             ident interface_ident)
      else if (not mod_inst.mod_inst_is_interface) && orig_mod_inst.mod_inst_is_interface
      then
        Error.type_error loc
          (Printf.sprintf
             !"Cannot redeclare interface %{Ident} from interface %{QualIdent} as module"
             ident interface_ident)
      else
        let* mod_inst_def = Rewriter.find_and_reify_module mod_inst.mod_inst_type in
        if
          not
          @@ Set.mem mod_inst_def.mod_decl.mod_decl_interfaces orig_mod_inst.mod_inst_type
        then
          Error.type_error loc
            (Printf.sprintf
               !"%s %{Ident} must implement interface %{QualIdent} according to \
                 interface %{QualIdent}"
               (Symbol.kind symbol |> String.capitalize)
               ident orig_mod_inst.mod_inst_type interface_ident)
        else
          match (mod_inst.mod_inst_def, orig_mod_inst.mod_inst_def) with
          | Some _, Some _ ->
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} was already defined in interface %{QualIdent}. It \
                     cannot be redefined"
                   (Symbol.kind symbol |> String.capitalize)
                   ident interface_ident)
          | None, Some _ ->
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} cannot be redeclared as abstract. It was already \
                     defined in interface %{QualIdent}"
                   (Symbol.kind symbol |> String.capitalize)
                   ident interface_ident)
          | _ -> Rewriter.return ())
  | ModDef mod_def, ModDef _orig_mod_def ->
      (* If LHS is free, then we are checking an inherited module against itself, which is OK. *)
      if is_free mod_def.mod_decl.mod_decl_status then Rewriter.return ()
      else
        (* Otherwise, RHS is being redefined, which is not OK. *)
        Error.type_error loc
          (Printf.sprintf
             !"%s %{Ident} was already defined in interface %{QualIdent}. It cannot be \
               redefined"
             (Symbol.kind symbol |> String.capitalize)
             ident interface_ident)
  | _ ->
      Error.type_error loc
        (Printf.sprintf
           !"Cannot redeclare %s %{Ident} from interface %{QualIdent} as %s"
           (Symbol.kind orig_symbol) ident interface_ident (Symbol.kind symbol))

(** Check that module `mod_ident` (M) implements interface `int_ident` (I) *)
let check_module_type mod_ident int_ident =
  let open Rewriter.Syntax in
  (* Get qualified idents and symbols of M and I *)
  let+ qual_mod_ident, mod_symbol = Rewriter.resolve_and_find mod_ident
  and+ qual_int_ident, int_symbol = Rewriter.resolve_and_find int_ident in
  (* Extract all interfaces implemented by M and check whether it is fully instantiated *)
  let interfaces, mod_is_instance =
    Rewriter.Symbol.extract mod_symbol ~f:(fun is_instance subst -> function
      | Ast.Module.ModDef mod_def ->
          (*Set.map (module QualIdent) mod_def.mod_decl.mod_decl_interfaces ~f:subst*)
          ( mod_def.mod_decl.mod_decl_interfaces,
            List.is_empty mod_def.mod_decl.mod_decl_formals || is_instance )
      | _ -> (Set.empty (module QualIdent), true))
  in
  (* Check whether I is fully instantiated *)
  let int_is_instance =
    Rewriter.Symbol.extract int_symbol ~f:(fun is_instance _subst -> function
      | Ast.Module.ModDef mod_def ->
          List.is_empty mod_def.mod_decl.mod_decl_formals || is_instance
      | _ -> true)
  in
  (* Check if I is one of M's interfaces *)
  if not (QualIdent.(qual_mod_ident = qual_int_ident) || Set.mem interfaces qual_int_ident)
  then
    Error.type_error (QualIdent.to_loc mod_ident)
      (Printf.sprintf
         !"%s %{QualIdent} does not implement interface %{QualIdent}"
         (Symbol.kind (Rewriter.Symbol.orig_symbol mod_symbol) |> String.capitalize)
         mod_ident int_ident)
  else if
    (* Make sure that I is the type of M itself rather than the expected type
         of the module obtained by instantiating *)
    int_is_instance && not mod_is_instance
  then
    Error.type_error (QualIdent.to_loc mod_ident)
      (Printf.sprintf
         !"%s %{QualIdent} first needs to be instantiated to obtain a module with \
           interface %{QualIdent}"
         (Symbol.kind (Rewriter.Symbol.orig_symbol mod_symbol) |> String.capitalize)
         mod_ident int_ident)

(** A module may implement several interfaces only if they share no ancestor: Raven
    identifies module types by path, so two routes to the same declaration give types that
    do not unify (see test/ci/front-end/fail/diamond_modules.rav). *)
let check_parents_disjoint ~loc parent_ancestors =
  let rec go = function
    | [] | [ _ ] -> ()
    | (p_mid, p_ancestors) :: rest ->
        List.iter rest ~f:(fun (q_mid, q_ancestors) ->
            let shared = Set.inter p_ancestors q_ancestors in
            match Set.min_elt shared with
            | None -> ()
            | Some common ->
                Error.type_error loc
                  (Printf.sprintf
                     !"Interfaces %{QualIdent} and %{QualIdent} cannot both be \
                       implemented here: they share the ancestor %{QualIdent}"
                     p_mid q_mid common));
        go rest
  in
  go parent_ancestors
