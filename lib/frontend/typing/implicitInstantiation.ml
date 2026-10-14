(** Implicit instantiation of functors, from the types of arguments and the expected type.
*)

open Base
open Ast
open Util
open TypingMonad
open TypingErrors

type field_formal = ident * (qual_ident * Module.field_def * Module.module_inst list)

type functor_signature = {
  formal_reps : (qual_ident * ident * ident) list;
  rep_suffixes : ident list list;
  field_formals : field_formal list;
}

type instantiation_solution = {
  bindings : (ident * type_expr) list;
  field_bindings : (ident * qual_ident) list;
}

let member_signatures ~only_calls member_ident (m : Module.t) =
  List.filter_map m.mod_def ~f:(function
    | Module.SymbolDef (CallDef call)
      when Ident.equal (Callable.source_ident call) member_ident
           || Ident.equal call.call_decl.call_decl_name member_ident ->
        let decl = call.call_decl in
        let formals, return_type =
          match (decl.call_decl_kind, decl.call_decl_returns) with
          | (Pred | Invariant), returns -> (decl.call_decl_formals @ returns, None)
          | _, [ r ] -> (decl.call_decl_formals, Some r.Type.var_type)
          | _, _ -> (decl.call_decl_formals, None)
        in
        Some (decl.call_decl_name, formals, return_type, decl.call_decl_loc_params)
    | SymbolDef (ConstrDef constr)
      when (not only_calls) && Ident.equal constr.constr_name member_ident ->
        Some (constr.constr_name, constr.constr_args, Some constr.constr_return_type, [])
    | SymbolDef (VarDef var)
      when (not only_calls) && Ident.equal var.var_decl.var_name member_ident ->
        Some (var.var_decl.var_name, [], Some var.var_decl.var_type, [])
    | _ -> None)

(** Resolves [qual_ident], or else the name [on_miss] rewrites it to; [None] if neither
    resolves. *)
let rec resolve_or_implicit_opt (qual_ident : qual_ident)
    ~(on_miss : unit -> qual_ident option t) : (qual_ident * Rewriter.Symbol.t) option t =
  let open Rewriter.Syntax in
  let* resolved = Rewriter.resolve_and_find_opt qual_ident in
  match resolved with
  | Some _ -> Rewriter.return resolved
  | None -> (
      let* rewritten = on_miss () in
      match rewritten with
      | Some rewritten_qual_ident -> Rewriter.resolve_and_find_opt rewritten_qual_ident
      | None -> Rewriter.return None)

(** [resolve_or_implicit_opt], but raising the ordinary "unknown identifier" error instead
    of returning [None] when [on_miss] doesn't apply either. *)
and resolve_or_implicit (qual_ident : qual_ident) ~(on_miss : unit -> qual_ident option t)
    : (qual_ident * Rewriter.Symbol.t) t =
  let open Rewriter.Syntax in
  let* resolved = resolve_or_implicit_opt qual_ident ~on_miss in
  match resolved with
  | Some resolved -> Rewriter.return resolved
  | None -> Rewriter.resolve_and_find qual_ident

(** Resolves [qi] as `<functor>.<member>`, for a functor eligible for implicit
    instantiation (see [ProgUtils.is_generic_functor]); [None] otherwise. *)
and resolve_generic_functor_prefix (qi : qual_ident) :
    (qual_ident * Module.t * ident) option t =
  let open Rewriter.Syntax in
  if List.is_empty (QualIdent.path qi) then Rewriter.return None
  else
    let functor_qi_written = QualIdent.pop qi in
    let member_ident = QualIdent.unqualify qi in
    let+ functor_resolved = lift (ProgUtils.resolve_generic_functor functor_qi_written) in
    Option.map functor_resolved ~f:(fun (functor_qual_ident, m) ->
        (functor_qual_ident, m, member_ident))

(** Whether [qi] is an instance of the functor [functor_qual_ident], or an alias of one.
*)
and resolves_to_instantiation_of ~(functor_qual_ident : qual_ident) (qi : qual_ident) :
    bool t =
  let open Rewriter.Syntax in
  let+ formal_module = instantiation_formal_module ~functor_qual_ident qi in
  Option.is_some formal_module

(** The modules that instantiate the formals of [functor_qual_ident] in [qi], if [qi] is
    an instance of it. A sealed instance resolves to the interface, so its arguments come
    from the symbol table. *)
and instantiation_formal_module ~(functor_qual_ident : qual_ident) (qi : qual_ident) :
    (ident -> qual_ident) option t =
  let open Rewriter.Syntax in
  let* tbl = Rewriter.get_table in
  match SymbolTbl.find_sealed_view qi tbl with
  | Some view when QualIdent.equal view.sealed_functor functor_qual_ident ->
      Rewriter.return
        (Some
           (fun formal -> List.Assoc.find_exn view.sealed_args formal ~equal:Ident.equal))
  | _ -> (
      let+ resolved = Rewriter.resolve_and_find_opt qi in
      match resolved with
      | Some (_, symbol)
        when QualIdent.equal (Rewriter.Symbol.orig_qid symbol) functor_qual_ident ->
          Some (QualIdent.append qi)
      | _ -> None)

(** The existing instance of the functor [m] that [typ] names, if any. *)
and resolve_existing_instantiation ~(functor_qual_ident : qual_ident) (m : Module.t)
    (typ : type_expr) : qual_ident option t =
  let open Rewriter.Syntax in
  match m.mod_decl.mod_decl_rep with
  | None -> Rewriter.return None
  | Some rep_ident -> (
      let* typ = TypeExpr.check typ in
      match typ with
      | App (Var qi, [], _)
        when Ident.equal (QualIdent.unqualify qi) rep_ident
             && not (List.is_empty (QualIdent.path qi)) ->
          let inst_qi = QualIdent.pop qi in
          let* is_inst = resolves_to_instantiation_of ~functor_qual_ident inst_qi in
          Rewriter.return (if is_inst then Some inst_qi else None)
      | _ -> Rewriter.return None)

(** The unification variables of [insts]: the abstract module members declared in
    [scope_qi] with a rep-typed interface, each as its rep within [scope_qi], its name and
    its rep ident. *)
and rep_vars_of_insts ~(scope_qi : qual_ident) (insts : Module.module_inst list) :
    (qual_ident * ident * ident) list t =
  let open Rewriter.Syntax in
  let+ vars =
    Rewriter.List.map insts ~f:(fun inst ->
        let+ rep = lift (ProgUtils.resolve_rep_ident inst.mod_inst_type) in
        Base.Option.map rep ~f:(fun (_, rep_ident) ->
            ( QualIdent.append (QualIdent.append scope_qi inst.mod_inst_name) rep_ident,
              inst.mod_inst_name,
              rep_ident )))
  in
  List.filter_opt vars

(** Unifies each pair of a type written in [m]'s body and the corresponding type at the
    call site, extending the solution [u] for the variables [formal_reps]. A structural
    approximation, without union-find or occurs check. *)
and unify_type_list ~(loc : location) ~(functor_qual_ident : qual_ident)
    ~(formal_reps : (qual_ident * ident * ident) list) ~(m_rep_suffixes : ident list list)
    (u : (ident * type_expr) list) (pairs : (type_expr * type_expr) list) :
    (ident * type_expr) list t =
  let open Rewriter.Syntax in
  (* Expanded, as the same type can be reached through different aliases (e.g. `Int` and
     `GenInst$$M$$Int.T.T`). *)
  let combine u formal_ident t2 =
    let* t2 = TypeExpr.expand_type_expr (t2 |> Type.set_ghost false) in
    match List.Assoc.find u formal_ident ~equal:Ident.equal with
    | Some prior when not (Type.equal prior t2) ->
        conflicting_inferred_types_error loc formal_ident functor_qual_ident prior t2
    | Some _ -> Rewriter.return u
    | None -> Rewriter.return (List.Assoc.add u formal_ident t2 ~equal:Ident.equal)
  in
  let is_rep_type qi =
    List.exists m_rep_suffixes ~f:(fun suffix ->
        List.equal Ident.equal (QualIdent.to_list qi)
          (QualIdent.to_list functor_qual_ident @ suffix))
  in
  let same_head c1 c2 =
    Type.equal
      (Type.App (c1, [], Type.dummy_attr) |> Type.set_ghost false)
      (Type.App (c2, [], Type.dummy_attr) |> Type.set_ghost false)
  in
  let rec go u = function
    | [] -> Rewriter.return u
    | (t1, t2) :: pairs ->
        let* u = unify_one u t1 t2 in
        go u pairs
  and unify_one u t1 t2 =
    (* Expand actual aliases for structural matching, retaining instance rep paths
       when recovering module arguments. Formals do not resolve outside [m]. *)
    let* t2 =
      let* t2 = TypeExpr.check t2 in
      match t1 with
      | Type.App (Var qi, [], _) when is_rep_type qi -> Rewriter.return t2
      | _ -> TypeExpr.expand_type_head t2
    in
    (* `Any`, `Num` (an operand of `+`) and `Perm` (an assertion, also met by `Bool`) say
       nothing about the formals. *)
    if
      Type.is_any (t1 |> Type.set_ghost false)
      || Type.is_any (t2 |> Type.set_ghost false)
      || Type.equal (t2 |> Type.set_ghost false) Type.num
      || Type.equal (t2 |> Type.set_ghost false) Type.perm
    then Rewriter.return u
    else
      (* [t1] is a formal's rep, or [m]'s own rep against an existing instance, or both
         sides recurse on matching heads. *)
      match
        List.find formal_reps ~f:(fun (rep_qi, _, _) ->
            match t1 with App (Var qi, [], _) -> QualIdent.equal rep_qi qi | _ -> false)
      with
      | Some (_, formal_ident, _) -> combine u formal_ident t2
      | None -> (
          match t1 with
          | App (Var qi, [], _) when is_rep_type qi -> (
              match t2 with
              | App (Var qi2, [], _) -> (
                  (* An instantiation's rep is the instance followed by one of the
                       rep's suffixes, depending on how far it has been expanded. *)
                  let qi2 = QualIdent.to_list qi2 in
                  let candidates =
                    List.filter_map m_rep_suffixes ~f:(fun suffix ->
                        let n = List.length qi2 - List.length suffix in
                        if n > 0 && List.equal Ident.equal (List.drop qi2 n) suffix then
                          Some (QualIdent.from_list (List.take qi2 n))
                        else None)
                  in
                  let* formal_module =
                    Rewriter.List.fold_left candidates ~init:None ~f:(fun found inst_qi ->
                        match found with
                        | Some _ -> Rewriter.return found
                        | None -> instantiation_formal_module ~functor_qual_ident inst_qi)
                  in
                  match formal_module with
                  | None -> Rewriter.return u
                  | Some formal_module ->
                      Rewriter.List.fold_left formal_reps ~init:u
                        ~f:(fun u (_, formal_ident, rep_ident) ->
                          combine u formal_ident
                            (Type.mk_var
                               (QualIdent.append (formal_module formal_ident) rep_ident)))
                  )
              | _ -> Rewriter.return u)
          (* A formal of type `Set[_]` accepts an argument of type `FinSet[_]`, but not
             the reverse. *)
          | App (Map, [ t1_elem; App (Bool, _, _) ], _) -> (
              let incompatible () = unify_types_error loc t1 t2 in
              match t2 with
              | App (FinSet, [ t2_elem ], _) -> go u [ (t1_elem, t2_elem) ]
              | App (Map, [ t2_elem; codomain ], _) ->
                  let* codomain = TypeExpr.expand_type_head codomain in
                  if Type.equal codomain Type.bool then go u [ (t1_elem, t2_elem) ]
                  else incompatible ()
              | _ -> incompatible ())
          | App (c1, args1, _) -> (
              match t2 with
              | App (c2, args2, _)
                when Int.equal (List.length args1) (List.length args2) && same_head c1 c2
                ->
                  go u (List.zip_exn args1 args2)
              | _ -> unify_types_error loc t1 t2))
  in
  go u pairs

(** Solves the field-typed formals of [functor_qual_ident] from the member's location
    arguments: a location formal's field `<functor>.<A>.<f>` names its formal `A`, and the
    argument `x.g` supplies `g`. Returns the solved formals with their fields, and the
    indices of the consumed arguments. *)
and solve_field_formals ~(claimed_location : expr -> expr t) ~(loc : location)
    ~(functor_qual_ident : qual_ident) ~(loc_params : qual_ident list)
    ~(arg_exprs : expr list) : ((ident * qual_ident) list * int list) t =
  let open Rewriter.Syntax in
  let indexed = List.mapi loc_params ~f:(fun i field -> (i, field)) in
  let+ solved =
    Rewriter.List.map indexed ~f:(fun (i, declared_field) ->
        let formal_ident = QualIdent.unqualify (QualIdent.pop declared_field) in
        let* arg =
          match List.nth arg_exprs i with
          | Some arg ->
              let+ arg = claimed_location arg in
              Some arg
          | None -> Rewriter.return None
        in
        match arg with
        | Some (Expr.App (Read, [ _; App (Var field, [], _) ], _)) ->
            let+ field = Rewriter.resolve field in
            (formal_ident, field, i)
        | Some arg ->
            field_argument_from_arg_error (Expr.to_loc arg) formal_ident
              functor_qual_ident
        | None -> field_argument_error loc formal_ident functor_qual_ident)
  in
  ( List.map solved ~f:(fun (formal_ident, field, _) -> (formal_ident, field)),
    List.map solved ~f:(fun (_, _, i) -> i) )

(** The module for [field_qi] as an implementation of [interface_qi]: solves the
    interface's abstract members by unifying its field's type with [field_qi]'s, and wraps
    each solution as a rep module. Its field is manifest, so it denotes the client's
    field. *)
and field_arg_module ~(loc : location) ~(insert_scope : qual_ident)
    ~(reference_scope : qual_ident) ~(interface_qi : qual_ident)
    ~(field : Module.field_def) ~(mod_members : Module.module_inst list)
    ~(field_qi : qual_ident) ~(field_type : type_expr) : qual_ident t =
  let open Rewriter.Syntax in
  let* formal_reps = rep_vars_of_insts ~scope_qi:interface_qi mod_members in
  let* bindings =
    (* Nothing to solve if the interface fixes its field's type; the adapter is then
       checked against the interface. *)
    if List.is_empty mod_members then Rewriter.return []
    else
      unify_type_list ~loc ~functor_qual_ident:interface_qi ~formal_reps
        ~m_rep_suffixes:[] []
        [ (field.field_type, field_type) ]
  in
  let* mod_bindings =
    Rewriter.List.map mod_members ~f:(fun member ->
        match List.Assoc.find bindings member.mod_inst_name ~equal:Ident.equal with
        | None ->
            module_member_inference_error loc member.mod_inst_name interface_qi field_qi
        | Some tp ->
            let* rep = lift (ProgUtils.resolve_rep_ident member.mod_inst_type) in
            let interface_qual_ident, rep_ident =
              match rep with
              | Some r -> r
              | None ->
                  Error.internal_error loc
                    (Printf.sprintf
                       !"module member %{Ident}'s constraint %{QualIdent} has no rep type"
                       member.mod_inst_name member.mod_inst_type)
            in
            let+ mod_qi =
              lift
                (ProgUtils.get_or_intros_rep_module ~loc ~f:!Rewriter.check_symbol_ref
                   ~insert_scope ~reference_scope ~interface_qual_ident ~rep_ident tp)
            in
            (member.mod_inst_name, mod_qi))
  in
  lift
    (ProgUtils.get_or_intros_field_module ~loc ~insert_scope ~reference_scope
       ~interface_qual_ident:interface_qi ~field ~field_qi ~field_type mod_bindings)

(** Discovers generic parameters without checking arguments or creating instances. *)
and discover_functor_signature ~functor_qual_ident (m : Module.t) =
  let open Rewriter.Syntax in
  let* solvers =
    Rewriter.List.map m.mod_decl.mod_decl_formals ~f:(fun formal ->
        lift (ProgUtils.classify_formal formal))
  in
  let field_formals =
    List.filter_map (List.zip_exn m.mod_decl.mod_decl_formals solvers)
      ~f:(fun (formal, solver) ->
        match solver with
        | Some (ProgUtils.ByField (interface_qi, field, mod_members)) ->
            Some (formal.mod_inst_name, (interface_qi, field, mod_members))
        | _ -> None)
  in
  let* formal_reps =
    rep_vars_of_insts ~scope_qi:functor_qual_ident m.mod_decl.mod_decl_formals
  in
  (* Include nested aliases of the functor's rep in inference. *)
  let m_rep_suffixes =
    match m.mod_decl.mod_decl_rep with
    | None -> []
    | Some rep_ident ->
        let functor_path = QualIdent.to_list functor_qual_ident in
        let aliased =
          List.find_map m.mod_def ~f:(function
            | Module.SymbolDef
                (TypeDef { type_def_name; type_def_expr = Some (App (Var qi, [], _)); _ })
              when Ident.equal type_def_name rep_ident ->
                let qi = QualIdent.to_list qi in
                if List.is_prefix qi ~prefix:functor_path ~equal:Ident.equal then
                  Some (List.drop qi (List.length functor_path))
                else if List.length qi > 1 then Some qi
                else None
            | _ -> None)
        in
        [ rep_ident ] :: Option.to_list aliased
  in
  Rewriter.return { formal_reps; rep_suffixes = m_rep_suffixes; field_formals }

(** Prepares a single target's arguments. Overload trials use the pure resolver. *)
and infer_single_instantiation ~check_expr ~claimed_location ~loc ~qual_ident
    ~functor_qual_ident (m : Module.t) ~signature ~member_formals ~return_type_opt
    ~loc_params ~arg_exprs ~expected_typ =
  let open Rewriter.Syntax in
  let omitted_are_implicit =
    List.drop member_formals (List.length arg_exprs)
    |> List.for_all ~f:(fun var_decl -> var_decl.Type.var_implicit)
  in
  if List.length member_formals < List.length arg_exprs || not omitted_are_implicit then
    arg_mismatch_error "Callable" loc (Type.Var qual_ident) (List.length member_formals)
  else
    let member_formals = List.take member_formals (List.length arg_exprs) in
    let field_formals = signature.field_formals in
    let* field_bindings, consumed =
      if List.is_empty field_formals then Rewriter.return ([], [])
      else
        solve_field_formals ~claimed_location ~loc ~functor_qual_ident ~loc_params
          ~arg_exprs
    in
    (* Field-dependent types are checked against the selected instance. *)
    let field_formal_paths =
      List.map field_formals ~f:(fun (formal_ident, _) ->
          QualIdent.to_list (QualIdent.append functor_qual_ident formal_ident))
    in
    let mentions_field_formal tp =
      Set.exists (Type.symbols tp) ~f:(fun qi ->
          let qi = QualIdent.to_list qi in
          List.exists field_formal_paths ~f:(fun prefix ->
              List.is_prefix qi ~prefix ~equal:Ident.equal))
    in
    (* This legacy peek elaborates arguments; never use it for candidate trials. *)
    let peek_arg formal_var_decl arg_expr =
      let* arg_expr =
        speculatively (check_expr arg_expr (Type.any |> Type.set_ghost_to expected_typ))
      in
      let arg_typ = Expr.to_type arg_expr in
      (* Empty literals and unresolved instances do not constrain generic parameters. *)
      if Type.contains_bot arg_typ then Rewriter.return None
      else Rewriter.return (Some (formal_var_decl.Type.var_type, arg_typ))
    in
    let* arg_pairs =
      Rewriter.List.map
        (List.mapi (List.zip_exn member_formals arg_exprs) ~f:(fun i p -> (i, p)))
        ~f:(fun (i, (formal_var_decl, arg_expr)) ->
          if
            List.mem consumed i ~equal:Int.equal
            || mentions_field_formal formal_var_decl.Type.var_type
          then Rewriter.return None
          else peek_arg formal_var_decl arg_expr)
    in
    let arg_pairs = List.filter_opt arg_pairs in
    let pairs =
      match return_type_opt with
      | Some return_type when not (mentions_field_formal return_type) ->
          (return_type, expected_typ) :: arg_pairs
      | _ -> arg_pairs
    in
    let* bindings =
      unify_type_list ~loc ~functor_qual_ident ~formal_reps:signature.formal_reps
        ~m_rep_suffixes:signature.rep_suffixes [] pairs
    in
    let missing =
      List.find m.mod_decl.mod_decl_formals ~f:(fun formal ->
          not
            (List.Assoc.mem bindings formal.mod_inst_name ~equal:Ident.equal
            || List.Assoc.mem field_bindings formal.mod_inst_name ~equal:Ident.equal))
    in
    Rewriter.return
      (match missing with
      | Some formal -> Error formal.mod_inst_name
      | None -> Ok { bindings; field_bindings })

(** Materializes an inferred solution, after selecting its member. *)
and instantiate_solution ~loc ~functor_qual_ident (m : Module.t) ~signature solution =
  if List.is_empty signature.field_formals then
    let arg_types =
      List.map m.mod_decl.mod_decl_formals ~f:(fun formal ->
          List.Assoc.find_exn solution.bindings formal.mod_inst_name ~equal:Ident.equal)
    in
    lift
      (ProgUtils.instantiate_type_functor ~loc ~f:!Rewriter.check_symbol_ref
         ~functor_qual_ident ~functor_mod_decl:m.mod_decl arg_types)
  else
    instantiate_mixed_functor ~loc ~functor_qual_ident ~functor_mod_decl:m.mod_decl
      ~bindings:solution.bindings ~field_bindings:solution.field_bindings
      ~field_formals:signature.field_formals

(** Resolves a generic member through discovery, inference, then instantiation. *)
and try_resolve_implicit_instantiation ~(check_expr : expr -> type_expr -> expr t)
    ~(claimed_location : expr -> expr t) ~(loc : location) ~(qual_ident : qual_ident)
    ~(arg_exprs : expr list) ?(only_calls = false) ~(expected_typ : type_expr) () :
    qual_ident option t =
  let open Rewriter.Syntax in
  let* prefix = resolve_generic_functor_prefix qual_ident in
  match prefix with
  | None -> Rewriter.return None
  | Some (functor_qual_ident, m, member_ident) -> (
      match member_signatures ~only_calls member_ident m with
      | [] -> Rewriter.return None
      | _ :: _ :: _ as members ->
          ambiguous_member_error loc member_ident (List.length members)
      | [ (declaration_ident, member_formals, return_type_opt, loc_params) ] -> (
          let* signature = discover_functor_signature ~functor_qual_ident m in
          let* inferred =
            infer_single_instantiation ~check_expr ~claimed_location ~loc ~qual_ident
              ~functor_qual_ident m ~signature ~member_formals ~return_type_opt
              ~loc_params ~arg_exprs ~expected_typ
          in
          match inferred with
          | Ok solution ->
              let+ instance =
                instantiate_solution ~loc ~functor_qual_ident m ~signature solution
              in
              Some (QualIdent.append instance declaration_ident)
          | Error formal_ident ->
              let* speculative = is_speculative in
              if speculative then Rewriter.return None
              else if
                List.Assoc.mem signature.field_formals formal_ident ~equal:Ident.equal
              then
                field_argument_without_location_error loc formal_ident functor_qual_ident
              else type_argument_inference_error loc formal_ident functor_qual_ident))

(** [ProgUtils.instantiate_type_functor] for a functor with at least one field-typed
    formal: each formal's argument module comes either from wrapping its solved type (as
    there) or from [field_arg_module], and the instantiation is keyed on the fields as
    well as the types. *)
and instantiate_mixed_functor ~(loc : location) ~(functor_qual_ident : qual_ident)
    ~(functor_mod_decl : Module.module_decl) ~(bindings : (ident * type_expr) list)
    ~(field_bindings : (ident * qual_ident) list)
    ~(field_formals :
       (ident * (qual_ident * Module.field_def * Module.module_inst list)) list) :
    qual_ident t =
  let open Rewriter.Syntax in
  let* bindings =
    Rewriter.List.map bindings ~f:(fun (formal_ident, tp) ->
        let+ tp = lift (!Rewriter.expand_type_expr_ref tp) in
        (formal_ident, tp))
  in
  (* The synthesized modules go beside whatever the arguments name: the solved types'
       own symbols, plus each argument field itself. *)
  let* insert_scope, reference_scope =
    lift
      (ProgUtils.find_insertion_scope_for_symbols
         (Set.union
            (ProgUtils.type_symbols (List.map bindings ~f:snd))
            (Set.of_list (module QualIdent) (List.map field_bindings ~f:snd))))
  in
  let* arg_module_qis =
    Rewriter.List.map functor_mod_decl.mod_decl_formals ~f:(fun formal ->
        match List.Assoc.find field_formals formal.mod_inst_name ~equal:Ident.equal with
        | Some (interface_qi, field, mod_members) ->
            let field_qi =
              List.Assoc.find_exn field_bindings formal.mod_inst_name ~equal:Ident.equal
            in
            let* _, field_symbol = Rewriter.resolve_and_find field_qi in
            let* field_symbol = Rewriter.Symbol.reify field_symbol in
            let field_type =
              match field_symbol with
              | Module.FieldDef fd -> fd.field_type
              | _ -> expected_field_error loc field_qi
            in
            field_arg_module ~loc ~insert_scope ~reference_scope ~interface_qi ~field
              ~mod_members ~field_qi ~field_type
        | None ->
            let tp =
              List.Assoc.find_exn bindings formal.mod_inst_name ~equal:Ident.equal
            in
            let* rep = lift (ProgUtils.resolve_rep_ident formal.mod_inst_type) in
            let interface_qual_ident, rep_ident =
              match rep with
              | Some r -> r
              | None ->
                  Error.internal_error loc
                    (Printf.sprintf
                       !"formal %{Ident}'s constraint %{QualIdent} has no rep type"
                       formal.mod_inst_name formal.mod_inst_type)
            in
            lift
              (ProgUtils.get_or_intros_rep_module ~loc ~f:!Rewriter.check_symbol_ref
                 ~insert_scope ~reference_scope ~interface_qual_ident ~rep_ident tp))
  in
  let inst_key =
    String.concat ~sep:","
      (List.map functor_mod_decl.mod_decl_formals ~f:(fun formal ->
           match
             List.Assoc.find field_bindings formal.mod_inst_name ~equal:Ident.equal
           with
           | Some field_qi -> QualIdent.to_string field_qi
           | None ->
               Type.to_string
                 (List.Assoc.find_exn bindings formal.mod_inst_name ~equal:Ident.equal)))
  in
  lift
    (ProgUtils.instantiate_functor_at_modules ~loc ~functor_qual_ident ~functor_mod_decl
       ~insert_scope ~reference_scope ~inst_key arg_module_qis)

(** [try_resolve_implicit_instantiation] for a destructor read `e.M.value`: without
    arguments, it succeeds only if [arg_typ], the type of `e`, names an existing instance
    of `M`. *)
and try_resolve_implicit_instantiation_destr ~(field_ident : qual_ident)
    ~(arg_typ : type_expr) : qual_ident option t =
  let open Rewriter.Syntax in
  let* prefix = resolve_generic_functor_prefix field_ident in
  match prefix with
  | None -> Rewriter.return None
  | Some (functor_qual_ident, m, member_ident) ->
      let has_member =
        List.exists m.mod_def ~f:(function
          | SymbolDef (DestrDef destr_def) ->
              Ident.equal destr_def.destr_name member_ident
          | _ -> false)
      in
      if not has_member then Rewriter.return None
      else
        let+ inst_qi_opt = resolve_existing_instantiation ~functor_qual_ident m arg_typ in
        Option.map inst_qi_opt ~f:(fun inst_qi -> QualIdent.append inst_qi member_ident)
