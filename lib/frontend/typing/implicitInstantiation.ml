(** Implicit instantiation of functors, from the types of arguments and the expected type.
*)

open Base
open Ast
open Util
open TypingMonad
open TypingErrors

(** Try plain resolution of [qual_ident]; on failure, invoke [on_miss] (one of
    [try_resolve_implicit_instantiation] / [try_resolve_implicit_instantiation_destr])
    and, if it rewrites to a new qual_ident, resolve that instead. [None] if neither
    applies. *)
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

(** Resolve [qi] as `<functor>.<member>`: split off the prefix, resolve it, and check it
    names a functor eligible for implicit instantiation (see
    [ProgUtils.is_generic_functor]). [None] if [qi] is unqualified, its prefix doesn't
    resolve, or isn't such a functor. Shared by [try_resolve_implicit_instantiation] and
    [try_resolve_implicit_instantiation_destr]. *)
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

(** Check whether [qi] is (an alias for) an instantiation of the functor resolved as
    [functor_qual_ident]: an instantiation's alias resolves back to [functor_qual_ident]
    itself, via [Rewriter.Symbol.orig_qid]. *)
and resolves_to_instantiation_of ~(functor_qual_ident : qual_ident) (qi : qual_ident) :
    bool t =
  let open Rewriter.Syntax in
  let+ formal_module = instantiation_formal_module ~functor_qual_ident qi in
  Option.is_some formal_module

(** If [qi] is an instantiation of the functor [functor_qual_ident], the module each of
    the functor's formals is instantiated with. A sealed instance resolves to the
    functor's interface rather than the functor, so its arguments are read off the symbol
    table's record of it. *)
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

(** Check whether [typ] (normalized via [TypeExpr.process_type_expr], in case it's a raw,
    self-referentially-read-back type) names an existing instantiation of functor [m];
    return that instantiation's qualified name on success. *)
and resolve_existing_instantiation ~(functor_qual_ident : qual_ident) (m : Module.t)
    (typ : type_expr) : qual_ident option t =
  let open Rewriter.Syntax in
  match m.mod_decl.mod_decl_rep with
  | None -> Rewriter.return None
  | Some rep_ident -> (
      let* typ = TypeExpr.process_type_expr typ in
      match typ with
      | App (Var qi, [], _)
        when Ident.equal (QualIdent.unqualify qi) rep_ident
             && not (List.is_empty (QualIdent.path qi)) ->
          let inst_qi = QualIdent.pop qi in
          let* is_inst = resolves_to_instantiation_of ~functor_qual_ident inst_qi in
          Rewriter.return (if is_inst then Some inst_qi else None)
      | _ -> Rewriter.return None)

(** The unification variables contributed by [insts] -- abstract module members declared
    inside [scope_qi], each constrained by a rep-typed interface. Each entry is (the
    member's rep qualident within [scope_qi], the member's name, its rep ident). Used both
    for a functor's formals and for a field interface's own module members. *)
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

(** Unify [pairs] against each other, threading (and extending) the partial solution [u]
    from the unification variables [formal_reps] to the concrete types they've been solved
    to so far. Each pair `(t1, t2)` is `t1`, a type written inside [m]'s own
    un-instantiated body (e.g. a parameter's declared type), against `t2`, the
    corresponding concrete type from the call site (e.g. an argument's inferred type).
    Deliberately a structural approximation, not a full algorithm (no union-find, no
    occurs check) -- see [unify_one] below for the three cases it distinguishes. *)
and unify_type_list ~(loc : location) ~(functor_qual_ident : qual_ident)
    ~(formal_reps : (qual_ident * ident * ident) list) ~(m_rep_suffixes : ident list list)
    (u : (ident * type_expr) list) (pairs : (type_expr * type_expr) list) :
    (ident * type_expr) list t =
  let open Rewriter.Syntax in
  (* Canonicalize via [expand_type_expr] before storing/comparing: two bindings for
       the same formal can be the same type reached through different alias chains
       (e.g. `Int` vs. `GenInst$$M$$Int.T.T`), which would otherwise look like a
       conflict. *)
  let combine u formal_ident t2 =
    let* t2 = TypeExpr.expand_type_expr (t2 |> Type.set_ghost false) in
    match List.Assoc.find u formal_ident ~equal:Ident.equal with
    | Some prior when not (Type.equal prior t2) ->
        Error.type_error loc
          (Printf.sprintf
             !"Cannot infer a single type for parameter %{Ident} of %{QualIdent}: found \
               both %{Type} and %{Type}"
             formal_ident functor_qual_ident prior t2)
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
    (* Normalize only [t2]: [t1] names [m]'s own formals/rep, which are by design
         unreachable via ordinary resolution from outside [m] -- it's only ever
         pattern-matched against [formal_reps]/[m_rep_suffixes] below, never resolved. *)
    let* t2 = TypeExpr.process_type_expr t2 in
    (* `Any`, the numeric placeholder `Num` (e.g. the expected type of an operand of
         `+`), and `Perm` (the expected type of an assertion, which a `Bool` also
         satisfies) say nothing about the formals. *)
    if
      Type.is_any (t1 |> Type.set_ghost false)
      || Type.is_any (t2 |> Type.set_ghost false)
      || Type.equal (t2 |> Type.set_ghost false) Type.num
      || Type.equal (t2 |> Type.set_ghost false) Type.perm
    then Rewriter.return u
    else
      (* Three cases: `t1` is a formal's rep (bind/check it against `t2`); `t1` is
           [m]'s own rep and `t2` is an existing instantiation (read off all formals at
           once); or both sides recurse structurally on matching head/arity. *)
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
          (* A formal declared `Set[_]` is satisfiable by a `FinSet[_]`-typed argument
               (FinSet[T] <: Set[T]) -- unify just the element position, same as the
               `Map`/`Map` structural case below would for matching heads. Not
               bidirectional: the reverse (formal `FinSet[_]`, argument `Set[_]`) is
               correctly rejected by the fallback below, since a plain Set can't satisfy
               a FinSet-typed formal (no downcast). *)
          | App (Map, [ t1_elem; App (Bool, _, _) ], _) -> (
              match t2 with
              | App (FinSet, [ t2_elem ], _) -> go u [ (t1_elem, t2_elem) ]
              | App (Map, [ t2_elem; App (Bool, _, _) ], _) -> go u [ (t1_elem, t2_elem) ]
              | _ ->
                  Error.type_error loc
                    (Printf.sprintf !"Cannot unify type %{Type} with type %{Type}" t1 t2))
          | App (c1, args1, _) -> (
              match t2 with
              | App (c2, args2, _)
                when Int.equal (List.length args1) (List.length args2) && same_head c1 c2
                ->
                  go u (List.zip_exn args1 args2)
              | _ ->
                  Error.type_error loc
                    (Printf.sprintf !"Cannot unify type %{Type} with type %{Type}" t1 t2))
          )
  in
  go u pairs

(** Solve the field-typed formals of [functor_qual_ident] from the member's location
    arguments. A location formal's declared field is `<functor>.<A>.<f>`, so its path
    names the formal it belongs to; the corresponding argument, written `x.g` at the call
    site, supplies `g`. Returns the solved formals paired with the fields they stand for,
    and the indices of the arguments consumed. *)
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
            Error.type_error (Expr.to_loc arg)
              (Printf.sprintf
                 !"Cannot infer the field argument for parameter %{Ident} of \
                   %{QualIdent} from this argument; pass a location, `x.f`, or write an \
                   explicit instantiation, e.g. `module M_X = %{QualIdent}[...]`"
                 formal_ident functor_qual_ident functor_qual_ident)
        | None ->
            Error.type_error loc
              (Printf.sprintf
                 !"Cannot infer a field argument for parameter %{Ident} of %{QualIdent}"
                 formal_ident functor_qual_ident))
  in
  ( List.map solved ~f:(fun (formal_ident, field, _) -> (formal_ident, field)),
    List.map solved ~f:(fun (_, _, i) -> i) )

(** Build the module standing for [field_qi] as an implementation of [interface_qi]: solve
    the interface's abstract module members by unifying its field's declared type against
    [field_qi]'s actual type, then wrap each solution as a rep module. This is what makes
    a field a functor argument -- the adapter's field is manifest, so it denotes the
    client's field rather than declaring one of its own. *)
and field_arg_module ~(loc : location) ~(insert_scope : qual_ident)
    ~(reference_scope : qual_ident) ~(interface_qi : qual_ident)
    ~(field : Module.field_def) ~(mod_members : Module.module_inst list)
    ~(field_qi : qual_ident) ~(field_type : type_expr) : qual_ident t =
  let open Rewriter.Syntax in
  let* formal_reps = rep_vars_of_insts ~scope_qi:interface_qi mod_members in
  let* bindings =
    (* Nothing to solve when the interface fixes its field's type outright (e.g. an
         `AtomicField` refined to `Int`); the field's own type is then checked when the
         adapter is verified against the interface. *)
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
            Error.type_error loc
              (Printf.sprintf
                 !"Cannot infer module member %{Ident} of %{QualIdent} from field \
                   %{QualIdent}; write an explicit instantiation instead"
                 member.mod_inst_name interface_qi field_qi)
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
                (ProgUtils.get_or_intros_rep_module ~loc ~f:!Rewriter.process_symbol_ref
                   ~insert_scope ~reference_scope ~interface_qual_ident ~rep_ident tp)
            in
            (member.mod_inst_name, mod_qi))
  in
  lift
    (ProgUtils.get_or_intros_field_module ~loc ~insert_scope ~reference_scope
       ~interface_qual_ident:interface_qi ~field ~field_qi ~field_type mod_bindings)

(** Try to resolve [qual_ident] (e.g. `M.foo`, already failed plain resolution) as a call
    into a member of an uninstantiated generic functor, implicitly instantiating it.
    [None] if [qual_ident] isn't `<functor>.<member>`-shaped, or the functor/member
    doesn't exist; once both exist, either succeeds or raises (the real problem is
    inference, not a typo).

    Type-typed formals are solved via [unify_type_list], unifying each argument's peeked
    type against its formal's declared type, plus the member's own return type against
    [expected_typ]. Field-typed formals are solved instead from the member's location
    arguments (see [solve_field_formals]): `l.bit` and `l.other` have the same type, so
    the variable ranges over symbol identity rather than over types. *)
and try_resolve_implicit_instantiation ~(process_expr : expr -> type_expr -> expr t)
    ~(claimed_location : expr -> expr t) ~(loc : location) ~(qual_ident : qual_ident)
    ~(arg_exprs : expr list) ?(only_calls = false) ~(expected_typ : type_expr) () :
    qual_ident option t =
  let open Rewriter.Syntax in
  let* prefix = resolve_generic_functor_prefix qual_ident in
  match prefix with
  | None -> Rewriter.return None
  | Some (functor_qual_ident, m, member_ident) -> (
      (* The member can be an ordinary callable, a data constructor, or a value -- all
           are addressable as `<module>.<member>(...)` and solved identically below, unless
           [only_calls] restricts this to callables: a speculative "is this a call?"
           peek (see the `Assign` statement's own peek in `process_basic_stmt`) must
           not also attempt -- and, on failure, hard-error on -- a constructor that
           was never going to become a `Stmt.Call` anyway; it should cleanly report
           "no match" instead and let the caller fall through to ordinary expression
           processing, where a correct [expected_typ] will actually be available. *)
      let member_info =
        List.find_map m.mod_def ~f:(function
          | SymbolDef (CallDef call_def)
            when Ident.equal (Callable.to_decl call_def).call_decl_name member_ident ->
              let call_decl = Callable.to_decl call_def in
              (* The parameters of a predicate or invariant after the `;` are kept
                   with the returns, but are arguments of an application. *)
              let formals, return_type =
                match (call_decl.call_decl_kind, call_decl.call_decl_returns) with
                | (Pred | Invariant), returns ->
                    (call_decl.call_decl_formals @ returns, None)
                | _, [ r ] -> (call_decl.call_decl_formals, Some r.Type.var_type)
                | _, _ -> (call_decl.call_decl_formals, None)
              in
              Some (formals, return_type, call_decl.call_decl_loc_params)
          | SymbolDef (ConstrDef constr_def)
            when (not only_calls) && Ident.equal constr_def.constr_name member_ident ->
              Some (constr_def.constr_args, Some constr_def.constr_return_type, [])
          | SymbolDef (VarDef var_def)
            when (not only_calls) && Ident.equal var_def.var_decl.var_name member_ident ->
              (* A value, such as `Seq.empty`, is solved from the expected type alone. *)
              Some ([], Some var_def.var_decl.var_type, [])
          | _ -> None)
      in
      match member_info with
      | None -> Rewriter.return None
      | Some (member_formals, return_type_opt, loc_params) -> (
          (* Trailing implicit ghost formals may be omitted at the call site, exactly
               as in [process_callable_args]; the arguments given line up with the
               leading formals and are all we can infer from. *)
          let omitted_are_implicit =
            List.drop member_formals (List.length arg_exprs)
            |> List.for_all ~f:(fun var_decl -> var_decl.Type.var_implicit)
          in
          if
            List.length member_formals < List.length arg_exprs || not omitted_are_implicit
          then
            arg_mismatch_error "Callable" loc (Type.Var qual_ident)
              (List.length member_formals)
          else
            let member_formals = List.take member_formals (List.length arg_exprs) in
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
            let* field_bindings, consumed =
              if List.is_empty field_formals then Rewriter.return ([], [])
              else
                solve_field_formals ~claimed_location ~loc ~functor_qual_ident ~loc_params
                  ~arg_exprs
            in
            (* A type written in terms of a field-solved formal (e.g. `A.E`) carries no
                 information the field hasn't already given, and peeking it would only
                 produce a spurious unification failure. The real check happens when the
                 call is reprocessed against the resolved instantiation. *)
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
            (* Peek each argument's type; the processed expr itself is discarded and
                 reprocessed once the instantiation is resolved. *)
            let peek_arg formal_var_decl arg_expr =
              let* arg_expr =
                speculatively
                  (process_expr arg_expr (Type.any |> Type.set_ghost_to expected_typ))
              in
              let arg_typ = Expr.to_type arg_expr in
              (* An underdetermined literal (e.g. `{||}`) peeked with no expected type,
                   or an argument that is itself an unresolved implicit instantiation of
                   some (possibly different) generic functor (e.g. `nil`, see
                   [speculatively] above), gives `Bot` for its missing type information --
                   that's not a real type argument to solve this instantiation with, but
                   it isn't necessarily fatal either: treat it as uninformative and move
                   on, the same way a [mentions_field_formal] argument already is below.
                   Other pairs -- a sibling argument, the return type against
                   [expected_typ] -- may still pin every formal; if they don't, the final
                   check once all pairs are gathered is what reports the error (correctly
                   deferred to speculative sub-attempts too, see
                   [try_resolve_implicit_instantiation]'s own "some formal unresolved"
                   check). *)
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
            let* formal_reps =
              rep_vars_of_insts ~scope_qi:functor_qual_ident m.mod_decl.mod_decl_formals
            in
            (* [m]'s rep, relative to [m], and the type of a nested module it
                 aliases, if any (e.g. `rep type T = L.T`): member signatures may
                 already refer to the latter. *)
            let m_rep_suffixes =
              match m.mod_decl.mod_decl_rep with
              | None -> []
              | Some rep_ident ->
                  let functor_path = QualIdent.to_list functor_qual_ident in
                  let aliased =
                    List.find_map m.mod_def ~f:(function
                      | Module.SymbolDef
                          (TypeDef
                             {
                               type_def_name;
                               type_def_expr = Some (App (Var qi, [], _));
                               _;
                             })
                        when Ident.equal type_def_name rep_ident ->
                          let qi = QualIdent.to_list qi in
                          if List.is_prefix qi ~prefix:functor_path ~equal:Ident.equal
                          then Some (List.drop qi (List.length functor_path))
                          else if List.length qi > 1 then Some qi
                          else None
                      | _ -> None)
                  in
                  [ rep_ident ] :: Option.to_list aliased
            in
            let* bindings =
              unify_type_list ~loc ~functor_qual_ident ~formal_reps ~m_rep_suffixes []
                pairs
            in
            match
              List.find m.mod_decl.mod_decl_formals ~f:(fun formal ->
                  not
                    (List.Assoc.mem bindings formal.mod_inst_name ~equal:Ident.equal
                    || List.Assoc.mem field_bindings formal.mod_inst_name
                         ~equal:Ident.equal))
            with
            | Some formal
              when List.Assoc.mem field_formals formal.mod_inst_name ~equal:Ident.equal ->
                (* [formal] just isn't determined yet -- not a mistake at this call
                     site. If this whole resolution attempt is itself happening
                     speculatively (i.e. this call is being peeked as an argument of
                     some enclosing, still-uninstantiated functor call, see
                     [peek_arg]), defer to whatever information the enclosing call
                     can supply instead of hard-erring here; the enclosing call
                     reprocesses this expression from source once it resolves, giving
                     this attempt a second, better-informed try. Only report the
                     error once nothing else is going to help. *)
                let* speculative = is_speculative in
                if speculative then Rewriter.return None
                else
                  Error.type_error loc
                    (Printf.sprintf
                       !"Cannot infer a field argument for parameter %{Ident} of \
                         %{QualIdent}, since this call takes no location; write an \
                         explicit instantiation, e.g. `module M_X = %{QualIdent}[...]`"
                       formal.mod_inst_name functor_qual_ident functor_qual_ident)
            | Some formal ->
                let* speculative = is_speculative in
                if speculative then Rewriter.return None
                else
                  Error.type_error loc
                    (Printf.sprintf
                       !"Cannot infer a type argument for parameter %{Ident} of \
                         %{QualIdent}; write an explicit instantiation, e.g. `module M_X \
                         = %{QualIdent}[...]`"
                       formal.mod_inst_name functor_qual_ident functor_qual_ident)
            | None ->
                let+ inst_qual_ident =
                  if List.is_empty field_formals then
                    let arg_types =
                      List.map m.mod_decl.mod_decl_formals ~f:(fun formal ->
                          List.Assoc.find_exn bindings formal.mod_inst_name
                            ~equal:Ident.equal)
                    in
                    lift
                      (ProgUtils.instantiate_type_functor ~loc
                         ~f:!Rewriter.process_symbol_ref ~functor_qual_ident
                         ~functor_mod_decl:m.mod_decl arg_types)
                  else
                    instantiate_mixed_functor ~loc ~functor_qual_ident
                      ~functor_mod_decl:m.mod_decl ~bindings ~field_bindings
                      ~field_formals
                in
                Some (QualIdent.append inst_qual_ident member_ident)))

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
              | _ ->
                  Error.type_error loc
                    (Printf.sprintf !"Expected a field, but found %{QualIdent}" field_qi)
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
              (ProgUtils.get_or_intros_rep_module ~loc ~f:!Rewriter.process_symbol_ref
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

(** The `Read`-expression (`expr1.M.value`) counterpart of
    [try_resolve_implicit_instantiation]. A destructor has no arguments to infer a type
    from, only [arg_typ] ([expr1]'s peeked type) -- so this only succeeds when [arg_typ]
    already names an existing instantiation of `M`, rewriting to that instantiation's
    destructor. *)
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
