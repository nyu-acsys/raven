open Base
open Ast
open ExtApi
open Util

(** Implements ADT ergonomics for `data { case ... }` types: a constructor-recognizer
    test, `xs is cons`, and `match` expressions. (A `match` *statement* -- arms whose
    bodies are statement blocks rather than expressions -- would be a separate
    construct on the `stmt_ext` extension point; it isn't implemented.) These are core
    Raven constructs, enabled by default (folded into
    `RavenCore` in lib/ext/ext.ml), not one more `--extension` choice -- ADT
    ergonomics is orthogonal to which resource-algebra extension is active.

    `xs is cons` tests whether `xs` (of some `data` type) was built with the `cons`
    constructor. Deliberately unqualified -- no `List.cons`/`MyType.cons` prefix --
    for the same reason plain field access (`xs.hd`) never needs one either: the
    constructor name is resolved against `xs`'s own (already known) type, exactly
    like `DataDestr` field resolution already works (see `typing.ml`'s `App (Read,
    [expr1; Var field_ident])` case). This also sidesteps a genuine grammar
    constraint: `List[T]`'s constructors are not reachable through the generic
    `qual_ident` grammar at all -- `ListExt`'s own parser fragment
    (`listExt_parser.mly`) hooks `List.cons(...)` in as a dedicated `LIST; DOT;
    IDENT` production on `unary_expr`, bypassing `qual_ident` entirely -- so a
    qualified `is` syntax would need a second, `List`-specific grammar production
    just to reach it. Resolving unqualified names against the scrutinee's own type
    works uniformly for both plain `data` types and `List` with no such special
    case. *)
module MatchExt (Cont : ListApi) = struct
  (* Every hook defaults to Cont's (including ListFns, since Cont : ListApi); only the
     ones actually overridden below need a definition. *)
  include Cont

  let lib_source = None

  (** One `case ctor(x, y) => ...` arm. [arm_ctor] is [None] for a wildcard/default
      arm (`case _ => ...`). Kept as bare, unqualified [Ident.t]s throughout --
      parsing, type-checking, and rewriting alike -- rather than switching to
      resolved [QualIdent.t]s after type-checking (the way [Is] does): a local
      variable's own reference is always just [QualIdent.from_ident] of its bare
      name (see e.g. [DecreasesExt]'s own `$decreases_...` locals, referenced the
      same way), so there is no resolved form to switch to for [arm_vars], and
      re-deriving [arm_ctor]'s matching variant from [as_data_type]/[find_variant]
      a second time in [rewrite_expr_ext] is cheap -- the same redundant-recompute
      trade DecreasesExt's own [is_wf_order_type] already makes on purpose. *)
  type match_arm = {
    arm_ctor : Ident.t option;
    arm_vars : Ident.t list;
  }

  (** Tag carries the resolved constructor's own qual_ident (e.g.
      `Library.ListM$Int.cons`, or `MyModule.MyType.cons` for a user `data` type) --
      resolved once, at type-checking time, against the scrutinee's own type; by the
      time [rewrite_expr_ext] runs, no further name resolution is needed. *)
  type Expr.expr_ext +=
    | Is of QualIdent.t
    | MatchExpr of match_arm list

  (* Resolves [tp] to its own qual_ident and variant list if it's a `data` type,
     [None] otherwise. Mirrors [DecreasesExt.as_data_type] (lib/ext/decreasesExt/
     decreasesExt.ml), extended with one more case: an extension-provided type (e.g.
     `List[T]`, represented during type-checking as its own `Type.type_ext`, not yet
     the real `data` type it's backed by -- see `ListExt.rewrite_type_ext`) is forced
     through the active chain's own [rewrite_type_ext] once, to resolve it down to
     the concrete, instantiated module type it's ultimately backed by, before retrying
     the same `Data` check. This covers `List` -- and any future extension-provided
     type backed by a real `data` type -- generically, with no dependency on
     `ListExt`'s internals. Only one level of indirection is unwound (matching
     `List[T]`'s own single-step resolution); an extension type backed by another,
     further-nested extension type is out of scope for now. *)
  let as_data_type (tp : type_expr) : (qual_ident * Type.variant_decl list) option Rewriter.t =
    let open Rewriter.Syntax in
    let data_type_of_var_type tp =
      match tp with
      | Type.App (Var qi, [], _) ->
        let* qi, symbol = Rewriter.resolve_and_find qi in
        let+ type_def = Rewriter.Symbol.reify_type_def (QualIdent.to_loc qi) symbol in
        (match type_def with
         | Some (Type.App (Data (data_qi, variant_decls), [], _)) -> Some (data_qi, variant_decls)
         | _ -> None)
      | _ -> Rewriter.return None
    in
    match tp with
    | Type.App (Var _, [], _) -> data_type_of_var_type tp
    | Type.App (TypeExt tag, args, _) ->
      let* tp' = Cont.rewrite_type_ext tag args (Type.to_loc tp) in
      data_type_of_var_type tp'
    | _ -> Rewriter.return None

  (* Finds the variant of [variant_decls] (belonging to data type [data_qi]) named
     [ctor_ident], if any, along with its own fully-qualified constructor qual_ident. *)
  let find_variant (data_qi : qual_ident) (variant_decls : Type.variant_decl list) (ctor_ident : ident) :
      (qual_ident * Type.variant_decl) option =
    let module_qi = QualIdent.pop data_qi in
    List.find_map variant_decls ~f:(fun (v : Type.variant_decl) ->
        if Ident.equal v.variant_name ctor_ident then Some (QualIdent.append module_qi v.variant_name, v)
        else None)

  (** Checks a `match`'s arm list against [variant_decls] before any arm body is
      type-checked: every named arm must name a real, distinct constructor of the
      scrutinee's data type; at most one wildcard (`case _`) arm is allowed, and it
      must be the last arm (simplest rule that has no soundness implication either
      way -- just an ergonomics/error-message choice); and, absent a wildcard, the
      named arms must cover every constructor exactly once. This is a plain
      [Ident]/set comparison against the symbol table's own record of the type's
      constructors -- no SMT call, so unlike ordinary verification conditions this
      is checked once, purely locally, as an ordinary type error. *)
  let check_arms_exhaustive (loc : location) (variant_decls : Type.variant_decl list) (arms : match_arm list) :
      unit Rewriter.t =
    let open Rewriter.Syntax in
    let variant_names = List.map variant_decls ~f:(fun (v : Type.variant_decl) -> v.variant_name) in
    let rec check_wildcard_is_last = function
      | [] | [ _ ] -> Rewriter.return ()
      | { arm_ctor = None; _ } :: _ :: _ ->
        Error.type_error loc "a wildcard ('_') match arm must be the last arm"
      | _ :: rest -> check_wildcard_is_last rest
    in
    let* () = check_wildcard_is_last arms in
    let named_ctors = List.filter_map arms ~f:(fun a -> a.arm_ctor) in
    let* () =
      match List.find_a_dup named_ctors ~compare:Ident.compare with
      | Some dup ->
        Error.type_error loc
          (Printf.sprintf "constructor '%s' is matched by more than one arm" (Ident.to_string dup))
      | None -> Rewriter.return ()
    in
    let* () =
      Rewriter.List.iter named_ctors ~f:(fun ctor ->
          if List.mem variant_names ctor ~equal:Ident.equal then Rewriter.return ()
          else
            Error.type_error loc
              (Printf.sprintf "'%s' is not a constructor of this data type" (Ident.to_string ctor)))
    in
    let has_wildcard = List.exists arms ~f:(fun a -> Option.is_none a.arm_ctor) in
    if has_wildcard then Rewriter.return ()
    else
      match List.filter variant_names ~f:(fun v -> not (List.mem named_ctors v ~equal:Ident.equal)) with
      | [] -> Rewriter.return ()
      | missing ->
        Error.type_error loc
          (Printf.sprintf "non-exhaustive match: missing case(s) for %s"
             (String.concat ~sep:", " (List.map missing ~f:Ident.to_string)))

  (* Shared by [Is]'s and [MatchExpr]'s [rewrite_expr_ext] below: a single field's
     destructor projection, and the reconstruct-and-compare recognizer condition for
     one variant, both relative to a data type's own home module [module_qi]. *)
  let destr_expr ~(loc : location) (module_qi : qual_ident) (scrutinee : expr) (fvd : var_decl) : expr =
    let destr_qi = QualIdent.append module_qi fvd.var_name in
    Expr.mk_app ~loc ~typ:fvd.var_type (DataDestr destr_qi) [ scrutinee ]

  let recognizer_cond ~(loc : location) (module_qi : qual_ident) (scrutinee : expr) (ctor_qi : qual_ident)
      (variant : Type.variant_decl) : expr =
    let reconstructed =
      Expr.mk_app ~loc ~typ:(Expr.to_type scrutinee) (DataConstr ctor_qi)
        (List.map variant.variant_args ~f:(destr_expr ~loc module_qi scrutinee))
    in
    Expr.mk_eq ~loc scrutinee reconstructed

  (** AstDef *)
  let expr_ext_to_string (expr_ext : Expr.expr_ext) : string =
    match expr_ext with
    | Is ctor_qi -> "is " ^ QualIdent.to_string ctor_qi
    | MatchExpr arms ->
      let arm_to_string (a : match_arm) =
        match a.arm_ctor with
        | None -> "case _ => ..."
        | Some ctor -> Printf.sprintf "case %s(%s) => ..." (Ident.to_string ctor)
            (String.concat ~sep:", " (List.map a.arm_vars ~f:Ident.to_string))
      in
      "match ... { " ^ String.concat ~sep:" " (List.map arms ~f:arm_to_string) ^ " }"
    | other -> Cont.expr_ext_to_string other

  let expr_ext_is_recognized (expr_ext : Expr.expr_ext) : bool =
    match expr_ext with
    | Is _ | MatchExpr _ -> true
    | other -> Cont.expr_ext_is_recognized other

  (* A pattern variable (or arm constructor) written `_`. Not a dedicated token -- see
     matchExt_parser.mly. *)
  let is_wildcard (id : ident) : bool = String.equal (Ident.name id) "_"

  (* Typing *)

  (** `match` arms are the only variable binders in Raven outside a quantifier, so this
      is the one construct that needs [disambiguate_expr_ext] (see its doc comment in
      [ExtApi]): each arm's pattern variables must be renamed to fresh names and pushed
      as a scope *before* the arm's body is walked, since the disambiguation pass runs
      ahead of all type-checking and would otherwise reject the body's references to
      them as unbound. Renaming also keeps an arm's variables from capturing -- or being
      captured by -- an identically-named local in the enclosing scope, exactly as it
      does for a quantifier's own bound variables.

      A pattern variable written `_` is renamed like any other but deliberately left out
      of the table, so it binds nothing (a body mentioning `_` gets the usual unbound
      error) and several `_`s in one arm don't collide as a redeclaration. *)
  let disambiguate_expr_ext (expr_ext : Expr.expr_ext) (expr_list : expr list) (expr_attr : Expr.expr_attr)
      (disam_tbl : ProgUtils.DisambiguationTbl.t) (functs : disambiguate_expr_functs) :
      (Expr.expr_ext * expr list) Rewriter.t =
    let open Rewriter.Syntax in
    match expr_ext, expr_list with
    | MatchExpr arms, scrutinee :: bodies when List.length bodies = List.length arms ->
      (* The scrutinee is outside every arm's scope; only the bodies see the patterns. *)
      let* scrutinee = functs.disambiguate_expr scrutinee disam_tbl in
      let disambiguate_arm ((arm : match_arm), body) =
        let arm_disam_tbl, arm_vars =
          List.fold_map arm.arm_vars ~init:(ProgUtils.DisambiguationTbl.push disam_tbl)
            ~f:(fun tbl pat_ident ->
              let loc = Ident.to_loc pat_ident in
              (* [~id:1] for the same reason [DisambiguationTbl.add_var_decl] uses it --
                 see there; arm variables named after the constructor's own fields
                 (`case cons(elem, tl)`) are exactly the case it protects. *)
              let fresh_ident = Ident.fresh loc ~id:1 (Ident.name pat_ident) in
              let tbl =
                if is_wildcard pat_ident then tbl
                else ProgUtils.DisambiguationTbl.add tbl loc pat_ident fresh_ident
              in
              (tbl, fresh_ident))
        in
        let+ body = functs.disambiguate_expr body arm_disam_tbl in
        ({ arm with arm_vars }, body)
      in
      let+ arms_and_bodies = Rewriter.List.map (List.zip_exn arms bodies) ~f:disambiguate_arm in
      let arms, bodies = List.unzip arms_and_bodies in
      (MatchExpr arms, scrutinee :: bodies)
    | _ -> Cont.disambiguate_expr_ext expr_ext expr_list expr_attr disam_tbl functs

  let type_check_expr (expr_ext : Expr.expr_ext) (expr_list : expr list) (expr_attr : Expr.expr_attr)
      (expected_typ : type_expr) (functs : type_check_expr_functs) : expr Rewriter.t =
    let open Rewriter.Syntax in
    match expr_ext, expr_list with
    | Is ctor_ident_as_qi, [ scrutinee ] ->
      (* The parser hands us the bare constructor name wrapped as an unqualified
         qual_ident (see matchExt_parser.mly); take its base back out. [unqualify]
         rather than [to_ident] because this can also be an *already* type-checked
         [Is], whose tag by then holds the resolved, qualified constructor ([to_ident]
         fails outright on those): a contract expression is type-checked more than
         once on some paths, e.g. when a callable is re-introduced via
         [Rewriter.introduce_typecheck_symbol']. Dropping the qualifier and
         re-resolving below just recomputes the same [ctor_qi], the same cheap
         redundant-recompute trade [arm_ctor] already makes by design (see
         [match_arm]) -- and keeps this hook idempotent, which is the property that
         actually matters here. *)
      let ctor_ident = QualIdent.unqualify ctor_ident_as_qi in
      (* [set_ghost_to expected_typ] on the scrutinee, as every core case in typing.ml
         does: testing the constructor of a ghost value is itself ghost, and is fine
         wherever a ghost value already is (a ghost block, a spec). Passing a bare
         [Type.any] would instead reject every ghost scrutinee outright. *)
      let* scrutinee = functs.process_expr scrutinee (Type.any |> Type.set_ghost_to expected_typ) in
      let* data_type = as_data_type (Expr.to_type scrutinee) in
      (match data_type with
       | None ->
         Error.type_error expr_attr.expr_loc
           "'is' can only test the constructor of a value of a `data` type"
       | Some (data_qi, variant_decls) ->
         (match find_variant data_qi variant_decls ctor_ident with
          | None ->
            Error.type_error expr_attr.expr_loc
              (Printf.sprintf "'%s' is not a constructor of this data type" (Ident.to_string ctor_ident))
          | Some (ctor_qi, _) ->
            let bool_typ = Type.bool |> Type.set_ghost_to expected_typ in
            functs.check_and_set
              (Expr.App (ExprExt (Is ctor_qi), [ scrutinee ], expr_attr))
              bool_typ bool_typ expected_typ))
    | MatchExpr arms, scrutinee :: bodies when List.length bodies = List.length arms ->
      (* Ghostness propagates into the scrutinee exactly as for [Is] above. *)
      let* scrutinee = functs.process_expr scrutinee (Type.any |> Type.set_ghost_to expected_typ) in
      let* data_type = as_data_type (Expr.to_type scrutinee) in
      (match data_type with
       | None ->
         Error.type_error expr_attr.expr_loc "a `match` scrutinee must have a `data` type"
       | Some (data_qi, variant_decls) ->
         let* () = check_arms_exhaustive expr_attr.expr_loc variant_decls arms in
         (* Every arm's body is checked against the same [expected_typ], exactly like
            a quantifier's inner expression ([typing.ml]'s [Binder] case) -- match is
            an ordinary expression whose result type is dictated by its surrounding
            context, not something this extension needs its own join/meet logic for. *)
         let* checked_bodies =
           Rewriter.List.map (List.zip_exn arms bodies) ~f:(fun (arm, body) ->
               match arm.arm_ctor with
               | None ->
                 if not (List.is_empty arm.arm_vars) then
                   Error.type_error expr_attr.expr_loc "a wildcard ('_') match arm cannot bind pattern variables"
                 else functs.process_expr body expected_typ
               | Some ctor_ident ->
                 (* [check_arms_exhaustive] above already guarantees [ctor_ident]
                    names a real variant of this data type. *)
                 let _, (variant : Type.variant_decl) =
                   Option.value_exn (find_variant data_qi variant_decls ctor_ident)
                 in
                 (match List.zip arm.arm_vars variant.variant_args with
                  | Unequal_lengths ->
                    Error.type_error expr_attr.expr_loc
                      (Printf.sprintf "'%s' expects %d pattern variable(s), but this arm binds %d"
                         (Ident.to_string ctor_ident) (List.length variant.variant_args)
                         (List.length arm.arm_vars))
                  | Ok pairs ->
                    let pat_var_decls =
                      List.map pairs ~f:(fun (pat_ident, (field_vd : var_decl)) ->
                          Type.mk_var_decl ~loc:(Ident.to_loc pat_ident) pat_ident field_vd.var_type)
                    in
                    let* _ = Rewriter.add_locals pat_var_decls in
                    functs.process_expr body expected_typ))
         in
         let result_typ = Expr.to_type (List.hd_exn checked_bodies) in
         functs.check_and_set
           (Expr.App (ExprExt (MatchExpr arms), scrutinee :: checked_bodies, expr_attr))
           result_typ result_typ expected_typ)
    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ functs

  (* Rewrites *)
  (** Lowers `xs is cons` to the established reconstruct-and-compare idiom already
      used by hand throughout this codebase (e.g. `decreasesExt.ml`'s auto-generated
      structural order): `xs == cons(xs.field_1, ..., xs.field_n)`. Z3's native
      datatype theory already reasons about constructor/selector axioms internally,
      so this costs about the same as a native recognizer/tester would -- no new
      backend support is needed. *)
  let rewrite_expr_ext (expr_ext : Expr.expr_ext) (expr_list : expr list) (expr_attr : Expr.expr_attr) :
      expr Rewriter.t =
    let open Rewriter.Syntax in
    match expr_ext, expr_list with
    | Is ctor_qi, [ scrutinee ] ->
      let* data_type = as_data_type (Expr.to_type scrutinee) in
      (match data_type with
       | Some (data_qi, variant_decls) ->
         let module_qi = QualIdent.pop data_qi in
         let variant =
           List.find_exn variant_decls ~f:(fun (v : Type.variant_decl) ->
               QualIdent.equal (QualIdent.append module_qi v.variant_name) ctor_qi)
         in
         Rewriter.return (recognizer_cond ~loc:expr_attr.expr_loc module_qi scrutinee ctor_qi variant)
       | None ->
         Error.internal_error expr_attr.expr_loc
           "MatchExt.Is reached the rewrite phase with a scrutinee that isn't a data type \
            (should have been rejected at type-checking time)")
    | MatchExpr arms, scrutinee :: bodies ->
      let* data_type = as_data_type (Expr.to_type scrutinee) in
      (match data_type with
       | None ->
         Error.internal_error expr_attr.expr_loc
           "MatchExt.MatchExpr reached the rewrite phase with a scrutinee that isn't a data type \
            (should have been rejected at type-checking time)"
       | Some (data_qi, variant_decls) ->
         let module_qi = QualIdent.pop data_qi in
         (* [arm_body] substitutes an arm's pattern variables (each just an ordinary,
            already-resolved local by this point -- see [type_check_expr]'s own
            [Rewriter.add_locals] above) for their destructor projections via
            [Expr.alpha_renaming], the same plain, already-established substitution
            mechanism used elsewhere in this codebase for qual_ident substitution.
            Skipped entirely for a wildcard arm, which binds no pattern variables
            (checked in [type_check_expr]). *)
         let arm_body (arm : match_arm) (body : expr) : expr =
           match arm.arm_ctor with
           | None -> body
           | Some ctor_ident ->
             let _, (variant : Type.variant_decl) =
               Option.value_exn (find_variant data_qi variant_decls ctor_ident)
             in
             let subst_map =
               List.zip_exn arm.arm_vars variant.variant_args
               |> List.map ~f:(fun (pat_ident, fvd) ->
                      (QualIdent.from_ident pat_ident, destr_expr ~loc:expr_attr.expr_loc module_qi scrutinee fvd))
               |> Map.of_alist_exn (module QualIdent)
             in
             Expr.alpha_renaming body subst_map
         in
         (* Right-nested `Ite` chain, one guard per named arm; the last arm (wildcard
            or, for an exhaustive match with no wildcard, the final named
            constructor) needs no guard at all -- [check_arms_exhaustive] already
            proved that if every earlier guard failed, this arm's condition is the
            only one that can hold. *)
         let rec build = function
           | [] ->
             Error.internal_error expr_attr.expr_loc
               "MatchExt.MatchExpr: empty match reached the rewrite phase \
                (should have been rejected at type-checking time)"
           | [ (arm, body) ] -> arm_body arm body
           | (arm, body) :: rest ->
             let body' = arm_body arm body in
             (match arm.arm_ctor with
              | None -> body'
              | Some ctor_ident ->
                let ctor_qi, variant = Option.value_exn (find_variant data_qi variant_decls ctor_ident) in
                let cond = recognizer_cond ~loc:expr_attr.expr_loc module_qi scrutinee ctor_qi variant in
                Expr.mk_ite ~loc:expr_attr.expr_loc cond body' (build rest))
         in
         Rewriter.return (build (List.zip_exn arms bodies)))
    | _ -> Cont.rewrite_expr_ext expr_ext expr_list expr_attr

  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
end
