open Base
open Ast
open Util

(* Longest prefix of [args] whose free variables are all among
   [formal_idents] -- walking stops at the first non-expressible argument,
   since a prefix can't skip past an unpinned link and still describe a
   meaningful narrower region. A variable bound by an enclosing quantifier
   (e.g. `exists nx :: ... is_queue(nx) ...`) is automatically treated as
   non-expressible here with no special-casing needed: it can never
   coincide with one of [formal_idents] (a different declaration's own
   formals, always a disjoint scope), so any argument built from it always
   truncates away on its own. *)
let truncate_to_formal_expressible (formal_idents : IdentSet.t)
    (args : Expr.t list) : Expr.t list =
  List.take_while args ~f:(fun arg ->
      Set.is_subset (Expr.local_vars arg) ~of_:formal_idents)

(* Given some declaration's own formals and the actual arguments used to
   mention it (e.g. `inv1`'s formals and the `[x, v]` used in a nested
   reference `inv1(x, v)` inside `inv2`'s body, or a callee's formals and
   actual call-site arguments), substitute those actual arguments into each
   of its mask entries, then truncate each to what's expressible via
   [caller_formal_idents] -- the formals of whoever's doing the mentioning.
   Length mismatch (formal/actual count differs) falls back to no
   substitution rather than aborting, mirroring the identical pattern in
   atomicityAnalysis.ml's [Call] handling. *)
let substitute_and_truncate_mask ~(mentioned_formals : Type.var_decl list)
    ~(actual_args : Expr.t list) ~(caller_formal_idents : IdentSet.t)
    (mask : Callable.mask) : Callable.mask =
  let renaming_map =
    match
      List.fold2 mentioned_formals actual_args
        ~init:(Map.empty (module QualIdent))
        ~f:(fun acc formal actual ->
          Map.set acc
            ~key:(QualIdent.from_ident formal.var_name)
            ~data:actual)
    with
    | Ok m -> m
    | Unequal_lengths -> Map.empty (module QualIdent)
  in
  List.map mask ~f:(fun (qi, args) ->
      let args = List.map args ~f:(fun e -> Expr.alpha_renaming e renaming_map) in
      (qi, truncate_to_formal_expressible caller_formal_idents args))

(* ------------------------------------------------------------------ *)
(* [call_decl_needs_mask] for [Proc]/[Lemma]: scanned purely from the
   callable's own [requires] clause -- never its body, never [ensures].
   This keeps mask computation modular: it never depends on inspecting any
   other callable's implementation, and an interface's abstract (bodyless)
   declaration and a concrete realization always agree, since [requires]
   is itself exact-match-enforced between them. A call inside the body to
   something that needs an invariant not already covered by this
   callable's own [requires] (or granted by an earlier call, see
   [call_decl_grants_mask] below) simply fails to verify at that call site
   -- which is exactly where a missing invariant belongs caught, rather
   than papered over by inferring it from the callee's mask. *)

(* Walks an expression collecting every [Pred]/[Invariant] application
   (declaration, kind, and its own argument list) reachable through
   [App]/[Binder] nesting -- the same traversal shape (and same [Pred] |
   [Invariant] filter) as [ProgUtils.expr_preds_mentioned], just
   additionally keeping each application's kind and arguments. *)
let rec expr_inv_applications (expr : Expr.t) :
    ((QualIdent.t * Callable.call_kind * Expr.t list) list, 'a) Rewriter.t_ext
    =
  let open Rewriter.Syntax in
  match expr with
  | Expr.App (Expr.Var qual_ident, args, _) ->
      let* _, (_, symbol, _) = Rewriter.resolve_and_find qual_ident in
      let* nested = Rewriter.List.map args ~f:expr_inv_applications in
      let nested = List.concat nested in
      (match symbol with
      | Module.CallDef { call_decl = { call_decl_kind = (Pred | Invariant) as kind; _ }; _ } ->
          Rewriter.return ((qual_ident, kind, args) :: nested)
      | _ -> Rewriter.return nested)
  | Expr.App (_, args, _) ->
      let+ nested = Rewriter.List.map args ~f:expr_inv_applications in
      List.concat nested
  | Expr.Binder (_, _, _, body, _) -> expr_inv_applications body

let compute_proc_lemma_mask (c : Callable.t) : (Callable.mask, 'a) Rewriter.t_ext
    =
  let open Rewriter.Syntax in
  let formal_idents =
    List.map c.call_decl.call_decl_formals ~f:(fun vd -> vd.var_name)
    |> Set.of_list (module Ident)
  in
  (* An implicit ghost formal occurring in an *atomic* spec is not an
     ordinary parameter -- it's the pseudo-quantified variable of a
     logically atomic triple (Iris's "current linearization-point state"),
     given a genuinely fresh value on every [openAU] to capture concurrent
     interference. So an invariant argument built from one can never be
     expressible in terms of "this callable's own formals" for mask
     purposes, even directly, unlike an ordinary (non-atomic) [requires] --
     there, an implicit ghost formal denotes one fixed value for the whole
     call, same as any other formal. Excluding implicit formals from what's
     "expressible" specifically when truncating an atomic spec's
     applications (below) is what forces e.g. `atomic requires p2(x)` down
     to the coarse `(p2, [])` rather than a `(p2, [x])` that can never be
     proven equal to whatever `openAU` later hands back. *)
  let non_implicit_formal_idents =
    List.filter_map c.call_decl.call_decl_formals ~f:(fun vd ->
        if vd.var_implicit then None else Some vd.var_name)
    |> Set.of_list (module Ident)
  in
  let* direct_applications =
    Rewriter.List.map c.call_decl.call_decl_precond ~f:(fun spec ->
        let+ apps = expr_inv_applications spec.spec_form in
        List.map apps ~f:(fun (qi, kind, args) -> (qi, kind, args, spec.spec_atomic)))
  in
  let direct_applications = List.concat direct_applications in
  (* Only an [Invariant] application itself needs mask room to unfold (a
     [Pred] is never mask-tracked at all, see atomicityAnalysis.ml's [Use]
     handling -- [Pred -> Rewriter.return stmt] with no mask interaction) --
     so only those contribute a [(qi, args)] entry of their own. *)
  let direct_entries =
    direct_applications
    |> List.filter_map ~f:(fun (qi, kind, args, spec_atomic) ->
           match kind with
           | Callable.Invariant ->
               let expressible =
                 if spec_atomic then non_implicit_formal_idents else formal_idents
               in
               Some (qi, truncate_to_formal_expressible expressible args)
           | Callable.Pred -> None
           | Callable.Func | Callable.Proc | Callable.Lemma -> assert false)
  in
  (* Either kind mentioned directly in [requires] can itself be a *nested*
     invariant -- its own body may assert another invariant's (or another
     pred's) existence (e.g. `inv queue(q) { ... is_queue(n) ... }`, or a
     [pred] wrapping an [inv]), which becomes unfoldable only *after*
     unfolding/consulting this one, never appearing in this callable's own
     [requires] text at all. [qi]'s own [call_decl_needs_mask] (computed by the
     [Pred | Invariant] branch below) already captures that -- but critically,
     it's expressed in terms of *[qi]'s own* formals (e.g. `queue`'s own
     mask names `is_queue`'s argument via whatever `queue`'s body calls
     it), not this callable's. It must be substituted through the actual
     arguments used to mention [qi] here, not pulled in verbatim --
     otherwise a specific nested reference degrades to a coarse,
     argument-less fallback that can needlessly collide with a more precise
     entry for the same declaration arriving via another directly-mentioned
     path -- exactly the redundant-entry situation [Callable.mask_canon]'s
     subsumption-collapsing (astDef.ml) exists to clean up when a coarse
     fallback is genuinely unavoidable, but which is better avoided at the
     source when it isn't. *)
  let* nested_entries =
    Rewriter.List.map direct_applications ~f:(fun (qi, _, args, spec_atomic) ->
        let* symbol = Rewriter.find_and_reify qi in
        match symbol with
        | CallDef
            {
              call_decl =
                {
                  call_decl_kind = Pred | Invariant;
                  call_decl_formals = mentioned_formals;
                  call_decl_needs_mask;
                  _;
                };
              _;
            } ->
            let expressible =
              if spec_atomic then non_implicit_formal_idents else formal_idents
            in
            (* [qi]'s own [call_decl_needs_mask] never carries the trivial
               "I need room for myself" baseline any more (see the doc
               comment on [fixpoint_compute_masks]'s [Pred | Invariant]
               branch) -- whatever's in it, including an entry naming [qi]
               itself, is genuine information from further nesting (e.g.
               `node`'s own mask entry `(is_queue, [])`, arrived at by
               chasing through `is_queue` mentioning `node` mentioning
               `is_queue` again under an existential -- see the module-level
               comment above), so nothing here needs excluding: pull all of
               it in. *)
            let nested_mask = Option.value call_decl_needs_mask ~default:[] in
            Rewriter.return
              (substitute_and_truncate_mask ~mentioned_formals ~actual_args:args
                 ~caller_formal_idents:expressible nested_mask)
        | _ -> Rewriter.return [])
  in
  let direct_entries = direct_entries @ List.concat nested_entries in
  Rewriter.return (Callable.mask_canon direct_entries)

(* ------------------------------------------------------------------ *)
(* Combined fixpoint driver for [call_decl_needs_mask]: both [Pred]/[Invariant]'s
   own mask and [Proc]/[Lemma]'s (above) can transitively depend on another
   [Pred]/[Invariant]'s mask -- through nested predicate mentions in the
   former's body, through a directly-[requires]-mentioned invariant's own
   nested mentions in the latter -- so both need iterating to a fixed point;
   [Func] is trivially mask-free (a pure expression can never unfold an
   invariant). *)
let fixpoint_compute_masks (c : Callable.t) : (Callable.t, bool) Rewriter.t_ext =
  let open Rewriter.Syntax in

  let* new_mask =
    match c.call_decl.call_decl_kind with
    | Pred | Invariant -> (
        (* No unconditional "I need room for myself" self-entry here (an
           earlier version of this algorithm added [(qi, [])] for every
           [Invariant] unconditionally): whoever mentions [qi] directly
           already contributes its own entry for [qi] independently, from
           its own [requires]/body text via [truncate_to_formal_expressible]
           -- so a bare self-entry only ever duplicates that. Worse, once
           merged via [Callable.mask_canon] a genuine, non-trivial widening
           this declaration's own nested chase produces (e.g. `node`'s
           `(is_queue, [])`, from mentioning `is_queue(nx)` under an
           existential) becomes value-indistinguishable from that trivial
           self-entry -- so keeping the self-entry around forced every
           consumer to guess which one it was looking at, and the only safe
           guess was "assume trivial and discard it", silently throwing the
           genuine case away too (this is what made `get_tail`'s recursive
           call to itself fail to verify: `is_queue`'s own correctly-widened
           `(is_queue, [])` was discarded as if it were only the trivial
           baseline). Omitting the self-entry entirely removes the ambiguity
           at the source: [call_decl_needs_mask] now holds only genuine
           nested information, so every consumer below can pull all of it in
           unconditionally, no exclusion needed. *)
        let formal_idents =
          List.map c.call_decl.call_decl_formals ~f:(fun vd -> vd.var_name)
          |> Set.of_list (module Ident)
        in

        match c.call_def with
        | FuncDef { func_body = Some body } ->
            (* Mirrors [compute_proc_lemma_mask]'s direct/nested split above,
               applied to an invariant/pred's own body instead of a
               proc/lemma's [requires] clause: a directly-mentioned
               [Invariant] application contributes its own (truncated)
               entry; either kind's own nested mask, if it has one, is
               pulled in too, substituted through the arguments used to
               mention it here (not verbatim -- see the long comment on
               [nested_entries] above for why that distinction matters, and
               what goes wrong -- redundant, coarser-than-necessary entries
               that can collide with a more precise entry for the same
               declaration arriving via a different path -- if it's
               skipped). *)
            let* applications = expr_inv_applications body in
            let direct_entries =
              applications
              |> List.filter_map ~f:(fun (qi, kind, args) ->
                     match kind with
                     | Callable.Invariant ->
                         Some (qi, truncate_to_formal_expressible formal_idents args)
                     | Callable.Pred -> None
                     | Callable.Func | Callable.Proc | Callable.Lemma -> assert false)
            in
            let* nested_entries =
              Rewriter.List.map applications ~f:(fun (qi, _, args) ->
                  let* symbol = Rewriter.find_and_reify qi in
                  match symbol with
                  | CallDef
                      {
                        call_decl =
                          {
                            call_decl_kind = Pred | Invariant;
                            call_decl_formals = mentioned_formals;
                            call_decl_needs_mask;
                            _;
                          };
                        _;
                      } ->
                      let nested_mask = Option.value call_decl_needs_mask ~default:[] in
                      Rewriter.return
                        (substitute_and_truncate_mask ~mentioned_formals
                           ~actual_args:args ~caller_formal_idents:formal_idents
                           nested_mask)
                  | _ -> Rewriter.return [])
            in
            Rewriter.return
              (Callable.mask_canon (direct_entries @ List.concat nested_entries))
        | FuncDef { func_body = None } -> Rewriter.return []
        | ProcDef _ -> assert false)
    | Lemma | Proc -> compute_proc_lemma_mask c
    | Func -> Rewriter.return []
  in

  if
    Option.is_some c.call_decl.call_decl_needs_mask
    && Callable.mask_equal new_mask (Option.value_exn c.call_decl.call_decl_needs_mask)
  then Rewriter.return c
  else
    let c =
      { c with call_decl = { c.call_decl with call_decl_needs_mask = Some new_mask } }
    in
    let* _ = Rewriter.set_user_state true in
    Rewriter.return c

let rec compute_iteration (m : Module.t) : (Module.t, bool) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let* flag = Rewriter.current_user_state in

  if flag then
    let* _ = Rewriter.set_user_state false in
    let* m = Rewriter.Module.rewrite_callables ~f:fixpoint_compute_masks m in
    compute_iteration m
  else Rewriter.return m

(* ------------------------------------------------------------------ *)
(* [call_decl_grants_mask]: a genuinely separate, auxiliary per-callable
   fact -- not part of any callable's contract, never checked against an
   interface's abstract view -- answering "does calling this callable hand
   the caller local mask credit, the way a local [fold] would?" Computed
   purely from [ensures] text (never the body): an [Invariant] application
   in [call_decl_postcond], fully expressible via this callable's own
   formals/returns. Available identically for an interface's own abstract
   (bodyless) declaration as for a concrete implementation -- closing what
   would otherwise be an interface/implementation asymmetry, since an
   abstract member has no body to derive anything from.

   Deliberately not narrowed by anything from [requires] (e.g. a
   `pass_through`-style callable whose [ensures] merely restates what it
   received, unconsumed, never genuinely re-[fold]ing anything): any
   resulting redundant/aliased credit is harmless, since a call or
   [unfold] whose own required entry could alias something the caller
   currently has open is independently guarded by [atomicityAnalysis.ml]'s
   [call_reentrancy_asserts]/[open_inv] -- that guard, not this
   computation, is what has to catch a genuine conflict, at the point the
   credit is actually acted on rather than at the point it's granted.

   Deliberately does *not* also scan the body for a genuine [fold] beyond
   what [ensures] states, even though that would find strictly more in
   some cases (a callable's own body-simulation used to be unioned in
   here). Any such extra entry is either redundant with what [ensures]
   already gives (same declaration, same args) or, when the folded
   resource isn't restated in [ensures], a phantom: it would clear this
   mask-level check, but no caller could ever actually spend it, since the
   only channel through which a resource crosses from a callee's body into
   a caller's proof state at all is [ensures] -- a body's own SL proof
   state can hold strictly more than what it postulates, and anything not
   restated there is simply framed away, never reaching the caller.
   Confirmed empirically, not just argued: the full test suite stays green
   with that body-simulation half removed entirely.

   Only entries fully expressible via this callable's own formals or
   return variables can ever be handed to a caller at all -- a caller has
   no way to substitute through a purely internal local, and (unlike
   [call_decl_needs_mask]'s truncation) *widening* to a shorter, coarser
   prefix here would be unsound: it would claim a whole sub-family is
   available when only one specific instance actually is (a fabrication of
   access to something never actually allocated, not mere reentrancy --
   [atomicityAnalysis.ml]'s call-site reentrancy guard only fires against
   an *already-open* instance of the same declaration, and does nothing to
   catch this). So an entry survives only if *every* position is
   expressible, not just a prefix. Atomic specs exclude implicit formals
   from what's expressible, same reasoning as [compute_proc_lemma_mask]:
   an implicit ghost formal in an atomic clause is [openAU]'s fresh
   pseudo-quantified variable, not a value fixed for the whole call.

   Purely a function of this callable's own declaration -- no dependency
   on any other callable's mask -- so, unlike [call_decl_needs_mask], this
   needs no fixpoint: one pass over the module suffices. *)
let rewrite_grants_mask (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  let* grants =
    match c.call_decl.call_decl_kind with
    | Func | Pred | Invariant -> Rewriter.return []
    | Lemma | Proc ->
        let formal_idents =
          List.map c.call_decl.call_decl_formals ~f:(fun vd -> vd.var_name)
          |> Set.of_list (module Ident)
        in
        let non_implicit_formal_idents =
          List.filter_map c.call_decl.call_decl_formals ~f:(fun vd ->
              if vd.var_implicit then None else Some vd.var_name)
          |> Set.of_list (module Ident)
        in
        let return_idents =
          List.map c.call_decl.call_decl_returns ~f:(fun vd -> vd.var_name)
          |> Set.of_list (module Ident)
        in
        let* ensures_applications =
          Rewriter.List.map c.call_decl.call_decl_postcond ~f:(fun spec ->
              let+ apps = expr_inv_applications spec.spec_form in
              List.map apps ~f:(fun (qi, kind, args) ->
                  (qi, kind, args, spec.spec_atomic)))
        in
        let entries =
          List.concat ensures_applications
          |> List.filter_map ~f:(fun (qi, kind, args, spec_atomic) ->
                 match kind with
                 | Callable.Invariant ->
                     let expressible =
                       Set.union
                         (if spec_atomic then non_implicit_formal_idents
                          else formal_idents)
                         return_idents
                     in
                     let prefix = truncate_to_formal_expressible expressible args in
                     if List.length prefix = List.length args then Some (qi, args)
                     else None
                 | Callable.Pred -> None
                 | Callable.Func | Callable.Proc | Callable.Lemma -> assert false)
        in
        Rewriter.return (Callable.mask_canon entries)
  in
  Rewriter.return
    { c with call_decl = { c.call_decl with call_decl_grants_mask = Some grants } }

(* ------------------------------------------------------------------ *)

let compute_masks (m : Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in
  let* m = Rewriter.eval_with_user_state ~init:true (compute_iteration m) in
  Rewriter.Module.rewrite_callables ~f:rewrite_grants_mask m

(** Checks that no module implementing an interface lets a newly-provided
    concrete definition of one of the interface's own abstract invariants or
    predicates depend on (i.e. include in its mask) another invariant that the
    same interface declares. An interface's own members are checked once,
    against the interface's abstract view; a caller reasoning about one of the
    interface's abstract members has no way to know that a later, concrete
    implementation made its mask grow to cover another of the interface's own
    invariants -- so if this were allowed, the interface's own members could
    silently stop verifying once instantiated concretely, without ever being
    re-checked.

    Scoped to modules declared as [module N : M { ... }] (i.e.
    [mod_decl_returns = Some M]). Functor instantiation doesn't go through
    this code path (see [Typing.merge_defs]) and isn't at risk the same way,
    since it only ever substitutes formals -- it never gives a fresh body to
    one of [M]'s own abstract members. *)

let owned_invariant_names (iface : Module.t) : Ident.t list =
  List.filter_map iface.mod_def ~f:(function
      | Module.SymbolDef
          (CallDef
            { call_decl = { call_decl_kind = Invariant; call_decl_name; _ }; _ })
        ->
          Some call_decl_name
      | _ -> None)

let abstract_pred_or_inv_names (iface : Module.t) : Ident.t list =
  List.filter_map iface.mod_def ~f:(function
      | Module.SymbolDef
          (CallDef
            ({
               call_decl = { call_decl_kind = (Pred | Invariant); call_decl_name; _ };
               _;
             } as call))
        when Callable.is_abstract call ->
          Some call_decl_name
      | _ -> None)

let find_call_by_name (mdef : Module.t) (name : Ident.t) : Callable.t option =
  List.find_map mdef.mod_def ~f:(function
      | Module.SymbolDef
          (CallDef ({ call_decl = { call_decl_name; _ }; _ } as call))
        when Ident.equal call_decl_name name ->
          Some call
      | _ -> None)

let check_interface_reach_back (n : Module.t) : (unit, 'a) Rewriter.t_ext =
  let open Rewriter.Syntax in
  match n.mod_decl.mod_decl_returns with
  | [] -> Rewriter.return ()
  | parents ->
      let* ifaces =
        Rewriter.List.map parents ~f:(fun (iface_qual_ident, _args) ->
            let+ iface = Rewriter.find_and_reify_module iface_qual_ident in
            (iface_qual_ident, iface))
      in
      (* Invariants owned by *any* parent, each tagged with the interface that
         declares it. With several parents a fresh concrete body can reach into
         an invariant declared by a different parent -- which neither parent's
         abstract view could anticipate, so it is the same hazard and must be
         rejected the same way. *)
      let* owned_by =
        let+ entries =
          Rewriter.List.map ifaces ~f:(fun (iface_qual_ident, iface) ->
              Rewriter.List.map (owned_invariant_names iface) ~f:(fun name ->
                  let+ qual_ident =
                    Rewriter.resolve (QualIdent.from_ident name)
                  in
                  (qual_ident, iface_qual_ident)))
        in
        Map.of_alist_reduce
          (module QualIdent)
          (List.concat entries)
          ~f:(fun first _ -> first)
      in
      let owned = Set.of_list (module QualIdent) (Map.keys owned_by) in
      Rewriter.List.iter ifaces ~f:(fun (iface_qual_ident, iface) ->
          Rewriter.List.iter (abstract_pred_or_inv_names iface) ~f:(fun name ->
              match find_call_by_name n name with
              | None -> Rewriter.return ()
              | Some call when Callable.is_abstract call -> Rewriter.return ()
              | Some call ->
                  let* self_qual_ident =
                    Rewriter.resolve (QualIdent.from_ident name)
                  in
                  let mask_names =
                    Option.value call.call_decl.call_decl_needs_mask ~default:[]
                    |> List.map ~f:fst
                    |> Set.of_list (module QualIdent)
                  in
                  let reach_back =
                    Set.remove (Set.inter mask_names owned) self_qual_ident
                  in
                  if Set.is_empty reach_back then Rewriter.return ()
                  else
                    (* With several parents the reached invariant need not belong
                       to the interface being implemented, so name its declarer
                       rather than assuming it is the same one. *)
                    let declarers =
                      Set.elements reach_back
                      |> List.filter_map ~f:(Map.find owned_by)
                      |> List.dedup_and_sort ~compare:QualIdent.compare
                    in
                    let same_interface =
                      match declarers with
                      | [ declarer ] -> QualIdent.equal declarer iface_qual_ident
                      | _ -> false
                    in
                    Error.type_error call.call_decl.call_decl_loc
                      (Stdlib.Format.asprintf
                         "%s %a implements interface %a's abstract %a, but its \
                          definition depends on %a, which %a %s"
                         (Symbol.kind (Module.CallDef call))
                         Ident.pr name QualIdent.pr iface_qual_ident Ident.pr name
                         (Util.Print.pr_list_comma QualIdent.pr)
                         (Set.elements reach_back)
                         (Util.Print.pr_list_comma QualIdent.pr)
                         declarers
                         (if same_interface then "also declares" else "declares"))))

let rec check_module_reach_back (m : Module.t) : (unit, 'a) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let* _ = Rewriter.enter_module m in
  let* () = check_interface_reach_back m in
  let* () =
    Rewriter.List.iter m.mod_def ~f:(function
        | Module.SymbolDef (ModDef mod_def) -> check_module_reach_back mod_def
        | _ -> Rewriter.return ())
  in
  let+ _ = Rewriter.exit_module m in
  ()

let check_no_interface_reach_back (m : Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in
  let+ () = check_module_reach_back m in
  m
