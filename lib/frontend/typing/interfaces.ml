(** Checks that a module conforms to the interfaces it implements. *)

open Base
open Ast
open Util
open TypingMonad
open TypingErrors

(** A value [var_def] implementing [orig_var_def]. *)
let check_implements_var (var_def : Stmt.var_def) (orig_var_def : Stmt.var_def)
    (interface_ident : qual_ident) (symbol : Symbol.t) (loc : location) (ident : ident) :
    unit t =
  let open Rewriter.Syntax in
  if var_def.var_decl.var_ghost && not orig_var_def.var_decl.var_ghost then
    Error.type_error loc
      (Printf.sprintf
         !"Cannot redeclare %s %{Ident} from interface %{QualIdent} as ghost"
         (Symbol.kind symbol) ident interface_ident)
  else if (not var_def.var_decl.var_ghost) && orig_var_def.var_decl.var_ghost then
    Error.type_error loc
      (Printf.sprintf
         !"Cannot redeclare ghost %s %{Ident} from interface %{QualIdent} as non-ghost"
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
               !"%s %{Ident} was already defined in interface %{QualIdent}. It cannot be \
                 redefined"
               (Symbol.kind symbol |> String.capitalize)
               ident interface_ident)
      | _ -> Rewriter.return ()

(** A callable [call_def] implementing [orig_call_def]: the same signature and, unless
    inherited, the same contract. *)
let check_implements_callable (call_def : Callable.t) (orig_call_def : Callable.t)
    (interface_ident : qual_ident) (symbol : Symbol.t) (orig_symbol : Symbol.t)
    (loc : location) (ident : ident) ~(manifest_subst : qual_ident Map.M(QualIdent).t) :
    unit t =
  let open Rewriter.Syntax in
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
             !"%s %{Ident} does not have the same number of parameters as %{Ident} in \
               interface %{QualIdent}"
             (Symbol.kind symbol) ident ident interface_ident)
  in

  if Poly.(call_def.call_decl.call_decl_kind <> orig_call_def.call_decl.call_decl_kind)
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
             !"%s %{Ident} does not have the same precondition as %{Ident} in interface \
               %{QualIdent}. Repeat its contract exactly, or omit it to inherit it"
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
             !"%s %{Ident} does not have the same postcondition as %{Ident} in interface \
               %{QualIdent}. Repeat its contract exactly, or omit it to inherit it"
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
             !"%s %{Ident} does not have the same opens clause as %{Ident} in interface \
               %{QualIdent}. Repeat its contract exactly, or omit it to inherit it"
             (Symbol.kind symbol) ident ident interface_ident)
    in
    match (call_def.call_def, orig_call_def.call_def) with
    | ProcDef { proc_body = Some _; _ }, ProcDef { proc_body = Some _; _ }
    | FuncDef { func_body = Some _; _ }, FuncDef { func_body = Some _; _ } ->
        Error.type_error loc
          (Printf.sprintf
             !"%s %{Ident} was already defined in interface %{QualIdent}. It cannot be \
               redefined"
             (Symbol.kind symbol |> String.capitalize)
             ident interface_ident)
    | ProcDef { proc_body = None; _ }, ProcDef { proc_body = Some _; _ }
    | FuncDef { func_body = None; _ }, FuncDef { func_body = Some _; _ } ->
        Error.type_error loc
          (Printf.sprintf
             !"%s %{Ident} cannot be redeclared as abstract. It was already defined in \
               interface %{QualIdent}"
             (Symbol.kind symbol |> String.capitalize)
             ident interface_ident)
    | _ -> Rewriter.return ()

(** A module [mod_def] implementing the module instance [orig_mod_inst]. *)
let check_implements_mod_inst (mod_def : Module.t) (orig_mod_inst : Module.module_inst)
    (interface_ident : qual_ident) (symbol : Symbol.t) (loc : location) (ident : ident) :
    unit t =
  if mod_def.mod_decl.mod_decl_is_interface && not orig_mod_inst.mod_inst_is_interface
  then
    Error.type_error loc
      (Printf.sprintf
         !"Cannot redeclare module %{Ident} from interface %{QualIdent} as interface"
         ident interface_ident)
  else if
    (not mod_def.mod_decl.mod_decl_is_interface) && orig_mod_inst.mod_inst_is_interface
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
             !"%s %{Ident} must implement interface %{QualIdent} according to interface \
               %{QualIdent}"
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
               !"%s %{Ident} was already defined in interface %{QualIdent}. It cannot be \
                 redefined"
               (Symbol.kind symbol |> String.capitalize)
               ident interface_ident)
      | _ -> Rewriter.return ()

(** A module instance [mod_inst] implementing the module instance [orig_mod_inst]. *)
let check_implements_mod_inst_by_inst (mod_inst : Module.module_inst)
    (orig_mod_inst : Module.module_inst) (interface_ident : qual_ident)
    (symbol : Symbol.t) (loc : location) (ident : ident) : unit t =
  let open Rewriter.Syntax in
  if mod_inst.mod_inst_is_interface && not orig_mod_inst.mod_inst_is_interface then
    Error.type_error loc
      (Printf.sprintf
         !"Cannot redeclare module %{Ident} from interface %{QualIdent} as interface"
         ident interface_ident)
  else if (not mod_inst.mod_inst_is_interface) && orig_mod_inst.mod_inst_is_interface then
    Error.type_error loc
      (Printf.sprintf
         !"Cannot redeclare interface %{Ident} from interface %{QualIdent} as module"
         ident interface_ident)
  else
    let* mod_inst_def = Rewriter.find_and_reify_module mod_inst.mod_inst_type in
    if
      not @@ Set.mem mod_inst_def.mod_decl.mod_decl_interfaces orig_mod_inst.mod_inst_type
    then
      Error.type_error loc
        (Printf.sprintf
           !"%s %{Ident} must implement interface %{QualIdent} according to interface \
             %{QualIdent}"
           (Symbol.kind symbol |> String.capitalize)
           ident orig_mod_inst.mod_inst_type interface_ident)
    else
      match (mod_inst.mod_inst_def, orig_mod_inst.mod_inst_def) with
      | Some _, Some _ ->
          Error.type_error loc
            (Printf.sprintf
               !"%s %{Ident} was already defined in interface %{QualIdent}. It cannot be \
                 redefined"
               (Symbol.kind symbol |> String.capitalize)
               ident interface_ident)
      | None, Some _ ->
          Error.type_error loc
            (Printf.sprintf
               !"%s %{Ident} cannot be redeclared as abstract. It was already defined in \
                 interface %{QualIdent}"
               (Symbol.kind symbol |> String.capitalize)
               ident interface_ident)
      | _ -> Rewriter.return ()

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
  | VarDef var_def, VarDef orig_var_def ->
      check_implements_var var_def orig_var_def interface_ident symbol loc ident
  | CallDef call_def, CallDef orig_call_def ->
      check_implements_callable call_def orig_call_def interface_ident symbol orig_symbol
        loc ident ~manifest_subst
  | ModDef mod_def, ModInst orig_mod_inst ->
      check_implements_mod_inst mod_def orig_mod_inst interface_ident symbol loc ident
  | ModInst mod_inst, ModInst orig_mod_inst ->
      check_implements_mod_inst_by_inst mod_inst orig_mod_inst interface_ident symbol loc
        ident
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

(** The names that [symbol] mentions. A nested module's mentions of its own members are
    left out. *)
let rec mentioned_names (symbol : Module.symbol) : Set.M(QualIdent).t =
  let empty = Set.empty (module QualIdent) in
  let arg_names acc = function
    | Module.ModArg qi -> Set.add acc qi
    | Module.TypeArg tp -> Type.symbols ~acc tp
  in
  let inst_names acc (inst : Module.module_inst) =
    let acc = Set.add acc inst.mod_inst_type in
    match inst.mod_inst_def with
    | None -> acc
    | Some (qi, args) -> List.fold args ~init:(Set.add acc qi) ~f:arg_names
  in
  match symbol with
  | TypeDef { type_def_expr; _ } ->
      Option.fold type_def_expr ~init:empty ~f:(fun acc tp -> Type.symbols ~acc tp)
  | FieldDef { field_type; field_alias; _ } ->
      let acc = Type.symbols field_type in
      Option.fold field_alias ~init:acc ~f:Set.add
  | VarDef { var_decl; var_init; _ } ->
      let acc = Type.symbols var_decl.var_type in
      Option.fold var_init ~init:acc ~f:(fun acc e -> Expr.symbols ~acc e)
  | CallDef { call_decl; call_def } ->
      (* A procedure's body is left out: callables may be used before their definition. *)
      let acc =
        List.fold (call_decl.call_decl_formals @ call_decl.call_decl_returns) ~init:empty
          ~f:(fun acc var_decl -> Type.symbols ~acc var_decl.var_type)
      in
      let acc =
        List.fold (call_decl.call_decl_precond @ call_decl.call_decl_postcond) ~init:acc
          ~f:(fun acc spec -> Expr.symbols ~acc spec.spec_form)
      in
      begin match call_def with
      | FuncDef { func_body = Some e } -> Expr.symbols ~acc e
      | _ -> acc
      end
  | ModInst inst -> inst_names empty inst
  | ModDef md ->
      let own =
        List.fold md.mod_def
          ~init:(Set.empty (module Ident))
          ~f:(fun acc -> function
            | Module.SymbolDef s -> Set.add acc (Symbol.to_name s) | Import _ -> acc)
      in
      let acc =
        List.fold md.mod_decl.mod_decl_returns ~init:empty ~f:(fun acc (qi, args) ->
            List.fold args ~init:(Set.add acc qi) ~f:arg_names)
      in
      let acc = List.fold md.mod_decl.mod_decl_formals ~init:acc ~f:inst_names in
      let acc =
        List.fold md.mod_def ~init:acc ~f:(fun acc -> function
          | Module.SymbolDef s -> Set.union acc (mentioned_names s)
          | Import _ -> acc)
      in
      Set.filter acc ~f:(fun qi ->
          match QualIdent.to_list qi with
          | first :: _ -> not (Set.mem own first)
          | [] -> true)
  | ConstrDef _ | DestrDef _ -> empty

(** The member of the module [mod_qual_ident] that [qi] names, if [qi] is relative to the
    module or qualified by it. *)
let member_of ~(mod_qual_ident : qual_ident) (qi : qual_ident) : ident option =
  let prefix = QualIdent.to_list mod_qual_ident in
  let comps = QualIdent.to_list qi in
  let comps =
    if List.is_prefix comps ~prefix ~equal:Ident.equal then
      List.drop comps (List.length prefix)
    else comps
  in
  List.hd comps

module IntGraph = Graph.Make (Int)

(** Orders the members [fixed] and [others] of the module [mod_qual_ident]. The members in
    [fixed] keep their order, as a module must be defined before it is used (see
    [ModuleTyping.check]), and each member comes after the members it mentions. Of the
    members ready to come next, those in [others] come first, in their order. Members that
    mention each other keep the order of [fixed] followed by [others]. *)
let order_members ~(mod_qual_ident : qual_ident) ~(fixed : Module.module_instr list)
    ~(others : Module.module_instr list) : Module.module_instr list =
  let members = Array.of_list (fixed @ others) in
  let num_fixed = List.length fixed in
  let index_of_name =
    Array.foldi members
      ~init:(Map.empty (module Ident))
      ~f:(fun i acc -> function
        | Module.SymbolDef s -> (
            match Map.add acc ~key:(Symbol.to_name s) ~data:i with
            | `Ok acc -> acc
            | `Duplicate -> acc)
        | Import _ -> acc)
  in
  let deps i =
    let mentioned =
      match members.(i) with
      | Module.SymbolDef s ->
          Set.fold (mentioned_names s) ~init:[] ~f:(fun acc qi ->
              match
                Option.bind (member_of ~mod_qual_ident qi) ~f:(Map.find index_of_name)
              with
              | Some j when j <> i -> j :: acc
              | _ -> acc)
      | Import _ -> []
    in
    if i > 0 && i < num_fixed then (i - 1) :: mentioned else mentioned
  in
  let graph =
    List.fold
      (List.range 0 (Array.length members))
      ~init:IntGraph.empty
      ~f:(fun g i ->
        IntGraph.add_edges (IntGraph.add_vertex g i) i (Set.of_list (module Int) (deps i)))
  in
  (* Of two members ready to come next, the one in [others] comes first. *)
  let compare_priority i j =
    let in_others k = k >= num_fixed in
    match (in_others i, in_others j) with
    | true, false -> -1
    | false, true -> 1
    | _ -> Int.compare i j
  in
  let sccs = List.map (IntGraph.topsort graph) ~f:(List.sort ~compare:Int.compare) in
  let scc_of =
    List.foldi sccs
      ~init:(Map.empty (module Int))
      ~f:(fun c acc scc ->
        List.fold scc ~init:acc ~f:(fun acc i -> Map.set acc ~key:i ~data:c))
  in
  let scc_deps =
    List.map sccs ~f:(fun scc ->
        List.fold scc
          ~init:(Set.empty (module Int))
          ~f:(fun acc i ->
            List.fold (deps i) ~init:acc ~f:(fun acc j ->
                Set.add acc (Map.find_exn scc_of j))))
    |> Array.of_list
  in
  let sccs = Array.of_list sccs in
  let scc_priority c =
    List.min_elt sccs.(c) ~compare:compare_priority |> Option.value_exn
  in
  let rec emit done_sccs acc remaining =
    if Set.is_empty remaining then List.rev acc
    else
      let ready =
        Set.filter remaining ~f:(fun c ->
            Set.for_all scc_deps.(c) ~f:(fun d -> d = c || Set.mem done_sccs d))
      in
      let next =
        Set.to_list ready
        |> List.min_elt ~compare:(fun c d ->
            compare_priority (scc_priority c) (scc_priority d))
        |> Option.value_exn
      in
      let acc = List.fold sccs.(next) ~init:acc ~f:(fun acc i -> members.(i) :: acc) in
      emit (Set.add done_sccs next) acc (Set.remove remaining next)
  in
  emit
    (Set.empty (module Int))
    []
    (Set.of_list (module Int) (List.range 0 (Array.length sccs)))

(** Merges the members of the interface [parent_ident] into [mod_def], the members of [m]:
    a member of the interface that [m] neither defines nor has as a formal is inherited.
    Returns the merged members, ordered by [order_members], and the members of the
    interface that [m] defines, to be checked against it. *)
let merge_defs ~(m : Module.t) ~(mod_qual_ident : qual_ident)
    ~(mod_def_formals : Module.module_instr list) ~(defined_symbols : Set.M(Ident).t)
    ~inherited_members ~parent_status ~parent_is_interface parent_ident parent_mod_def
    mod_def =
  (* A non-callable member without a definition, like those the check below rejects in a
     non-interface module. Callables are left out: a free callable without a body had
     its body dropped when it was freed. *)
  let symbol_is_abstract = function
    | Module.TypeDef { type_def_expr = None; _ }
    | ModInst { mod_inst_def = None; _ }
    | VarDef { var_decl = { var_const = true; _ }; var_init = None; _ } ->
        true
    | _ -> false
  in
  (* Included files, the standard library among them, are marked [MachineFree] so that
     they are not verified again. An abstract member that a concrete module inherits
     from one of their interfaces must not arrive free, or the module would owe neither
     its definition nor, for an axiom, its proof. A [free] written by the user stays
     [UserFree]. Abstract callables are never freed, so this concerns types, values and
     module instances. *)
  let un_free_inherited symbol =
    match (parent_status, Symbol.free_status symbol) with
    | MachineFree, (NotFree | MachineFree)
      when parent_is_interface
           && (not m.mod_decl.mod_decl_is_interface)
           && symbol_is_abstract symbol ->
        Module.set_symbol_status NotFree symbol
    | _ -> symbol
  in
  let formals =
    List.fold_left
      ~init:(Set.empty (module Ident))
      ~f:(fun acc -> function
        | Module.SymbolDef (ModInst mod_inst) -> Set.add acc mod_inst.mod_inst_name
        | _ -> acc)
      mod_def_formals
  in
  (* The member of the interface [parent_symbol] as inherited by [m]. *)
  let inherit_member parent_symbol =
    let parent_symbol_ident = Symbol.to_name parent_symbol in
    let annotate_error_msg = function
      | Module.CallDef ({ call_decl; _ } as call) as symbol ->
          let annotate_spec spec =
            let error =
              ( Error.RelatedLoc,
                Symbol.to_loc parent_symbol,
                Printf.sprintf
                  !"%s %{Ident} inherited from %s %{QualIdent}.%{Ident}"
                  (Symbol.kind symbol |> String.capitalize)
                  parent_symbol_ident (Symbol.kind parent_symbol) parent_ident
                  parent_symbol_ident )
            in
            {
              spec with
              Stmt.spec_error = Stmt.mk_const_spec_error error :: spec.Stmt.spec_error;
            }
          in
          let call_decl =
            {
              call_decl with
              call_decl_precond = List.map ~f:annotate_spec call_decl.call_decl_precond;
              call_decl_postcond = List.map ~f:annotate_spec call_decl.call_decl_postcond;
              call_decl_loc = m.mod_decl.mod_decl_loc;
            }
          in
          Module.CallDef { call with call_decl }
      | symbol -> symbol
    in
    Logs.debug (fun m -> m !"Inheriting symbol %{Ident}" parent_symbol_ident);
    match un_free_inherited parent_symbol with
    | CallDef call when not @@ Callable.is_abstract call ->
        Module.CallDef (Callable.set_machine_free call)
    | CallDef ({ call_decl = { call_decl_kind = Lemma; _ }; _ } as call)
      when Callable.is_abstract call && not m.mod_decl.mod_decl_is_interface ->
        let loc = m.mod_decl.mod_decl_loc in
        (* Keep 'auto' flag for everything but RA associativity axioms *)
        let auto =
          call.call_decl.call_decl_is_auto
          && String.(call.call_decl.call_decl_name |> Ident.name <> "compAssoc")
        in
        let call =
          {
            Callable.call_decl = { call.call_decl with call_decl_is_auto = auto };
            call_def = ProcDef { proc_body = Some (Stmt.mk_skip ~loc) };
          }
        in
        let call =
          if is_free m.mod_decl.mod_decl_status then Callable.set_machine_free call
          else call
        in
        annotate_error_msg (CallDef call)
    | ModDef mod_def -> ModDef (Module.set_machine_free mod_def)
    | symbol -> annotate_error_msg symbol
  in
  let is_member = function
    | Module.SymbolDef (ConstrDef _ | DestrDef _) -> false
    | SymbolDef _ -> true
    | Import _ -> false
  in
  let to_check, inherited =
    List.fold parent_mod_def
      ~init:(Map.empty (module Ident), [])
      ~f:(fun (to_check, inherited) -> function
        | Module.SymbolDef parent_symbol as instr when is_member instr ->
            let name = Symbol.to_name parent_symbol in
            if Set.mem formals name || Set.mem defined_symbols name then
              (Map.add_exn to_check ~key:name ~data:parent_symbol, inherited)
            else (
              inherited_members := (parent_ident, parent_symbol) :: !inherited_members;
              (to_check, Module.SymbolDef (inherit_member parent_symbol) :: inherited))
        | _ -> (to_check, inherited))
  in
  let fixed =
    List.filter mod_def ~f:(function
      | Module.SymbolDef (ConstrDef _ | DestrDef _) -> false
      | _ -> true)
  in
  (order_members ~mod_qual_ident ~fixed ~others:(List.rev inherited), to_check)

(** The parents of [m]: its return types, the interfaces it implements, its first parent
    and that parent's formals, and its members merged with theirs, with those to check
    against the interfaces. *)
let merge_parents ~(m : Module.t) ~(is_root : bool) ~(mod_qual_ident : qual_ident)
    ~(mod_def : Module.module_instr list) ~(mod_def_formals : Module.module_instr list)
    ~(defined_symbols : Set.M(Ident).t) ~inherited_members =
  let open Rewriter.Syntax in
  (* Disjointness is checked on the parents as declared, before the substitution below
       renames each parent to this module. *)
  let* () =
    match m.mod_decl.mod_decl_returns with
    | [] | [ _ ] -> Rewriter.return ()
    | returns ->
        let+ parent_ancestors =
          Rewriter.List.map returns ~f:(fun (mid, _args) ->
              let* qual_ident, symbol = Rewriter.resolve_and_find mid in
              let+ symbol = Rewriter.Symbol.reify symbol in
              match symbol with
              | Module.ModDef interface ->
                  (mid, Set.add interface.mod_decl.mod_decl_interfaces qual_ident)
              | _ -> (mid, Set.singleton (module QualIdent) qual_ident))
        in
        check_parents_disjoint ~loc:m.mod_decl.mod_decl_loc parent_ancestors
  in
  let* parents =
    Rewriter.List.map m.mod_decl.mod_decl_returns ~f:(fun (mid, args) ->
        Logs.debug (fun mm ->
            mm
              !"ModuleTyping.check: module %{Ident}: checking return type %{QualIdent}"
              (Symbol.to_name (ModDef m)) mid);
        let* qual_interface_ident, interface_symbol = Rewriter.resolve_and_find mid in
        (* A parameterized parent's formals are substituted by its arguments first, then
             its name by this module's; in the other order, a mapping for `Base.A` would
             no longer match. *)
        let* arg_subst =
          Rewriter.List.map args ~f:(function
            | Module.ModArg qi ->
                let base = QualIdent.unqualify qi in
                if
                  QualIdent.is_local qi
                  && List.exists m.mod_decl.mod_decl_formals ~f:(fun formal ->
                      Ident.equal formal.mod_inst_name base)
                then
                  (* An argument naming one of this module's formals: these are not in
                       the symbol table yet, so point at the formal directly. *)
                  Rewriter.return (QualIdent.append mod_qual_ident base)
                else
                  let+ qi = Rewriter.resolve qi in
                  qi
            | Module.TypeArg tp ->
                Error.type_error (Type.to_loc tp)
                  "An inherited interface must be applied to modules, not to bare types; \
                   name a module implementing the parameter's interface instead")
        in
        let interface_symbol =
          match interface_symbol with
          | _ when List.is_empty arg_subst -> interface_symbol
          | _ -> (
              let formals =
                Rewriter.Symbol.extract interface_symbol
                  ~f:(fun _is_instance _subst -> function
                  | Ast.Module.ModDef mod_def -> mod_def.mod_decl.mod_decl_formals
                  | _ -> [])
              in
              match List.zip formals arg_subst with
              | Ok pairs ->
                  List.fold pairs ~init:interface_symbol ~f:(fun sym (formal, arg_qi) ->
                      Rewriter.Symbol.extend_subst
                        ( QualIdent.append qual_interface_ident formal.mod_inst_name,
                          QualIdent.to_list arg_qi )
                        sym)
              | Unequal_lengths ->
                  arg_mismatch_error "Interface" (QualIdent.to_loc mid) (Type.Var mid)
                    (List.length formals))
        in
        let interface_symbol =
          Rewriter.Symbol.extend_subst
            (qual_interface_ident, QualIdent.to_list mod_qual_ident)
            interface_symbol
        in

        (* Read off the symbol as resolved: the reified declaration below does not carry
             the flag. *)
        let parent_is_interface =
          Rewriter.Symbol.extract interface_symbol ~f:(fun _ _ -> function
            | Ast.Module.ModDef md -> md.mod_decl.mod_decl_is_interface
            | _ -> false)
        in
        let* interface_symbol = Rewriter.Symbol.reify interface_symbol in
        let* () =
          Rewriter.Logs.debug (fun printers mm ->
              mm
                !"ModuleTyping.check: %{Ident}: checking return type %a: reified; \n\
                 \ qual_interface_ident: %{QualIdent} \n\
                 \ mid: %{QualIdent}"
                (Symbol.to_name (ModDef m)) printers.pr_symbol interface_symbol
                qual_interface_ident mid)
        in
        Rewriter.return
          (qual_interface_ident, mid, arg_subst, parent_is_interface, interface_symbol))
  in
  let parent_defs =
    List.filter_map parents ~f:(function
      | qual_interface_ident, mid, args, parent_is_interface, ModDef interface ->
          Some (qual_interface_ident, mid, args, parent_is_interface, interface)
      | _ -> None)
  in
  match parent_defs with
  | [] ->
      let mod_ident = QualIdent.from_ident m.mod_decl.mod_decl_name in
      let interfaces =
        if is_root then m.mod_decl.mod_decl_interfaces
        else Set.add m.mod_decl.mod_decl_interfaces mod_qual_ident
      in
      Rewriter.return
        ([], interfaces, mod_ident, None, (m.mod_def, Map.empty (module Ident)))
  | first_parent :: _ ->
      (* Merge each parent in turn, threading the accumulated definition, so
             a later parent sees earlier parents' members as already defined. *)
      let returns, interfaces, formals, merged, to_check =
        List.fold parent_defs
          ~init:
            ([], Set.empty (module QualIdent), None, m.mod_def, Map.empty (module Ident))
          ~f:(fun
              (returns, interfaces, formals, mod_def, to_check)
              (qual_interface_ident, _mid, args, parent_is_interface, interface)
            ->
            let merged, to_check' =
              merge_defs ~m ~mod_qual_ident ~mod_def_formals ~defined_symbols
                ~inherited_members ~parent_status:interface.mod_decl.mod_decl_status
                ~parent_is_interface qual_interface_ident interface.mod_def mod_def
            in
            let to_check =
              Map.fold to_check' ~init:to_check ~f:(fun ~key ~data acc ->
                  match Map.add acc ~key ~data:(qual_interface_ident, data) with
                  | `Ok acc -> acc
                  | `Duplicate ->
                      Error.type_error m.mod_decl.mod_decl_loc
                        (Printf.sprintf
                           !"Member %{Ident} is declared by more than one of the \
                             interfaces %s implements; a module cannot inherit two \
                             declarations of the same name"
                           key
                           (Ident.to_string
                              (ProgUtils.source_module_name m.mod_decl.mod_decl_name))))
            in
            (* Only an unapplied parameterised parent imposes its formals on
                   this module; an applied one supplied them as arguments. *)
            let formals =
              match (formals, args) with
              | Some _, _ | None, _ :: _ -> formals
              | None, [] ->
                  if List.is_empty interface.mod_decl.mod_decl_formals then None
                  else Some interface.mod_decl.mod_decl_formals
            in
            ( (qual_interface_ident, List.map args ~f:(fun qi -> Module.ModArg qi))
              :: returns,
              Set.union interfaces
                (Set.add interface.mod_decl.mod_decl_interfaces qual_interface_ident),
              formals,
              merged,
              to_check ))
      in
      let qual_first, _, _, _, _ = first_parent in
      Rewriter.return
        (List.rev returns, interfaces, qual_first, formals, (merged, to_check))

(** A callable that omits its contract -- no `requires`, `ensures` or `opens` -- inherits
    the contract of the interface member it implements, with the interface's parameters
    renamed to its own. *)
let inherit_contract (symbols_to_check : (qual_ident * Module.symbol) Map.M(Ident).t) =
  function
  | Module.SymbolDef (CallDef ({ call_decl; _ } as call)) as instr
    when List.is_empty call_decl.call_decl_precond
         && List.is_empty call_decl.call_decl_postcond
         && Option.is_none call_decl.call_decl_opens -> (
      match Map.find symbols_to_check call_decl.call_decl_name with
      | Some (interface_ident, (CallDef orig as orig_symbol)) -> (
          let orig_decl = orig.call_decl in
          let renaming =
            List.zip
              (orig_decl.call_decl_formals @ orig_decl.call_decl_returns)
              (call_decl.call_decl_formals @ call_decl.call_decl_returns)
          in
          match renaming with
          | Unequal_lengths -> instr
          | Ok pairs ->
              let map =
                List.fold pairs
                  ~init:(Map.empty (module QualIdent))
                  ~f:(fun map ((orig_var : var_decl), (var : var_decl)) ->
                    Map.set map
                      ~key:(QualIdent.from_ident orig_var.var_name)
                      ~data:(Expr.from_var_decl var))
              in
              let rename e = Expr.alpha_renaming e map in
              let inherited =
                ( Error.RelatedLoc,
                  Symbol.to_loc orig_symbol,
                  Printf.sprintf
                    !"Contract inherited from %s %{QualIdent}.%{Ident}"
                    (Symbol.kind orig_symbol) interface_ident call_decl.call_decl_name )
              in
              let inherit_spec (spec : Stmt.spec) =
                {
                  spec with
                  spec_form = rename spec.spec_form;
                  spec_trigs = List.map spec.spec_trigs ~f:(List.map ~f:rename);
                  spec_error = spec.spec_error @ [ Stmt.mk_const_spec_error inherited ];
                }
              in
              let call_decl =
                {
                  call_decl with
                  call_decl_precond = List.map orig_decl.call_decl_precond ~f:inherit_spec;
                  call_decl_postcond =
                    List.map orig_decl.call_decl_postcond ~f:inherit_spec;
                  call_decl_opens =
                    Option.map orig_decl.call_decl_opens
                      ~f:(List.map ~f:(fun (qi, args) -> (qi, List.map args ~f:rename)));
                }
              in
              let () =
                EditorAnnotations.record_inherited_contract
                  ~member:call_decl.call_decl_name ~source:interface_ident
                  ~source_loc:(Symbol.to_loc orig_symbol) ~renaming:pairs orig_decl
              in
              Module.SymbolDef (CallDef { call with call_decl }))
      | _ -> instr)
  | instr -> instr
