open Base
open Ast
open Ast.Stmt
open Ast.Expr
open Util

type au_token = {
  token : Expr.t;
  source_token : Expr.t;
  callable : QualIdent.t;
  callable_args : expr list;
  implicit_bound_vars : expr list;
  (* Where the [openAU] was, so a never-committed update can point back at it. *)
  au_loc : location;
  (* As [inv_updated]/[inv_updated_flag] of [invs], since the [openAU]. *)
  au_updated : bool;
  au_updated_flag : Expr.t;
}

type invs = {
  inv_name : QualIdent.t;
  inv_args : Expr.t list;
  (* Where the [unfold] was, so a never-folded instance can point back at it. *)
  inv_loc : location;
  (* Snapshot of the values of all of the instance's arguments, implicit ones
     included, at the moment it was opened, in a fresh ghost local. The
     matching [fold] must restore exactly these: a local variable in
     [inv_args] can be reassigned in between, and an invariant's implicit
     arguments must never change. *)
  inv_snapshot : Expr.t;
  (* The mask entry consumed from [atomicity_check.mask] to open this
     instance (see [open_inv]); restored verbatim on the matching close (see
     [close_inv]). *)
  inv_consumed_mask_entry : Callable.mask_entry;
  (* Whether a statement that may make the instance less closable happened since it was
     opened (see [keeps_closable]). Only then, or if the call takes resources, can the
     state on abort of an atomic call fail to close it (see [abort_check]). *)
  inv_updated : bool;
  (* A ghost [Bool] local, false at the [unfold] and set by every such statement, so that
     the check at an atomic call runs only on paths that performed one. *)
  inv_updated_flag : Expr.t;
}

(* A predicate instance unfolded while an atomic update or invariant is open, with the
   witnesses that refold it: the variables the [unfold] bound its existentials to. *)
type unfolded_pred = {
  pred_name : QualIdent.t;
  pred_args : Expr.t list;
  pred_witnesses : (Ident.t * Expr.t) list;
  pred_loc : location;
}

type atomicity_check = {
  au_opened : au_token list;
  au_bindings : IdentSet.t; (* Locals known to hold this call's token. *)
  invs_opened : invs list;
  (* Predicate instances unfolded since an update or instance was opened, most recent
     first, without those folded or whose arguments were reassigned since. If a call
     aborts, they are refolded (see [abort_check]). *)
  preds_unfolded : unfolded_pred list;
  atomic_step_taken : bool;
  mask : Callable.mask;
  (* Set while analysing the body of a physically atomic block. The block as a
     whole already cost one step in the enclosing context, and no intermediate
     state inside it is observable, so step counting is suspended within.
     Invariant and atomic-update tracking continues, so anything opened inside
     must still be closed inside. *)
  in_atomic_block : bool;
  namespace_draft : NamespaceInference.t option;
  separation : NamespaceContract.separation_requirement list;
  callees : QualIdentSet.t;
}

type namespace_analysis = {
  callable : Callable.t;
  separation : NamespaceContract.separation_requirement list;
  callees : QualIdentSet.t;
}

let compare_separation left right =
  let compare_mask = List.compare Callable.compare_mask_entry in
  match compare_mask left.NamespaceContract.left right.NamespaceContract.left with
  | 0 ->
      begin match compare_mask left.right right.right with
      | 0 -> Loc.compare left.loc right.loc
      | order -> order
      end
  | order -> order

let union_separation left right =
  List.dedup_and_sort (left @ right) ~compare:compare_separation

(* Cross-namespace assumptions are lifted to whole families, without local binders. *)
let require_separation ~loc required (state : atomicity_check) =
  match state.namespace_draft with
  | None -> state
  | Some _ ->
      let separation =
        List.concat_map required ~f:(fun (head, _) ->
            List.filter_map state.invs_opened ~f:(fun opened ->
                let opened_head = Callable.MaskHead.Invariant opened.inv_name in
                if Callable.equal_mask_head head opened_head then None
                else
                  let left, right =
                    if Callable.compare_mask_head head opened_head < 0 then
                      (head, opened_head)
                    else (opened_head, head)
                  in
                  Some
                    {
                      NamespaceContract.left = [ (left, []) ];
                      right = [ (right, []) ];
                      loc;
                    }))
      in
      { state with separation = union_separation state.separation separation }

(* Renders an open instance the way the [unfold] named it, e.g. [i(x)]. *)
let inv_to_string (inv : invs) : string =
  let name = Ident.to_string (QualIdent.unqualify inv.inv_name) in
  match inv.inv_args with
  | [] -> name
  | args ->
      name ^ "(" ^ String.concat ~sep:", " (List.map args ~f:Expr.to_source_string) ^ ")"

(* Something is still open at the end of a callable's body. Report it where the
   omission is actually detected -- the end of the body -- and point back at the
   [unfold]/[openAU] that opened it, which is the part of the program the reader
   has to go find. Anything else still open is named as a further related
   location rather than being left for a second run to discover. *)
let unclosed_error ~(body_loc : location) (state : atomicity_check) : 'a =
  let inv_entry inv =
    ( Printf.sprintf "Missing fold for unfolded invariant %s" (inv_to_string inv),
      inv.inv_loc,
      Printf.sprintf "%s was unfolded here" (inv_to_string inv) )
  in
  let au_entry au =
    let token = Expr.to_source_string au.source_token in
    ( Printf.sprintf "Missing commitAU or abortAU for open atomic update %s" token,
      au.au_loc,
      Printf.sprintf "%s was opened here" token )
  in
  let entries =
    List.map state.invs_opened ~f:inv_entry @ List.map state.au_opened ~f:au_entry
  in
  match entries with
  | [] -> Error.internal_error body_loc "unclosed_error called with nothing left open"
  | (msg, rel_loc, rel_msg) :: rest ->
      Error.fail_with
        ((Error.Verification Error.Unclosed, Loc.last_char body_loc, msg)
        :: (Error.RelatedLoc, rel_loc, rel_msg)
        :: List.map rest ~f:(fun (msg, rel_loc, _) -> (Error.RelatedLoc, rel_loc, msg)))

let list_remove_first (lst : 'a list) ~(f : 'a -> bool) : 'a list =
  let rec go = function [] -> [] | x :: xs -> if f x then xs else x :: go xs in
  go lst

let same_open_au (au1 : au_token) (au2 : au_token) : bool =
  Expr.alpha_equal au1.token au2.token
  && QualIdent.equal au1.callable au2.callable
  && List.equal Expr.alpha_equal au1.callable_args au2.callable_args
  && List.equal Expr.alpha_equal au1.implicit_bound_vars au2.implicit_bound_vars

(* Multiset equality of open instances; closes match by identity, so order is
   irrelevant. [Expr.compare] is stricter than [alpha_equal] only on bound
   variable names, which can merely cause a (sound) rejection. *)
let same_open_invs (l1 : invs list) (l2 : invs list) : bool =
  let sorted l =
    List.map l ~f:(fun inv -> Callable.invariant_mask_entry inv.inv_name inv.inv_args)
    |> List.sort ~compare:Callable.compare_mask_entry
  in
  List.equal (fun e1 e2 -> Callable.compare_mask_entry e1 e2 = 0) (sorted l1) (sorted l2)

(* At a join, [into]'s entries are carried forward, but each arm froze its own
   snapshot. Assignments, for the end of [from]'s arm, that copy [from]'s
   snapshots into [into]'s, so the kept snapshots are defined on both paths.
   Assumes [same_open_invs from into]; the reentrancy guard keeps the sort
   keys unique, so sorting pairs up matching instances. *)
let snapshot_sync_stmts ~loc ~(from : invs list) ~(into : invs list) : Stmt.t list =
  let sorted l =
    List.sort l ~compare:(fun i1 i2 ->
        Callable.compare_mask_entry
          (Callable.invariant_mask_entry i1.inv_name i1.inv_args)
          (Callable.invariant_mask_entry i2.inv_name i2.inv_args))
  in
  let copy ~src ~dst =
    if Expr.alpha_equal src dst then None
    else Some (Stmt.mk_assign ~loc ~is_init:true [ Expr.to_qual_ident dst ] src)
  in
  List.concat_map
    (List.zip_exn (sorted from) (sorted into))
    ~f:(fun (src, dst) ->
      let snapshot =
        if List.is_empty dst.inv_args then None
        else copy ~src:src.inv_snapshot ~dst:dst.inv_snapshot
      in
      List.filter_opt
        [ snapshot; copy ~src:src.inv_updated_flag ~dst:dst.inv_updated_flag ])

(* As [snapshot_sync_stmts], for the update flag of the open atomic update. *)
let au_flag_sync_stmts ~loc ~(from : au_token list) ~(into : au_token list) : Stmt.t list
    =
  List.filter_map (List.zip_exn from into) ~f:(fun (src, dst) ->
      if Expr.alpha_equal src.au_updated_flag dst.au_updated_flag then None
      else
        Some
          (Stmt.mk_assign ~loc ~is_init:true
             [ Expr.to_qual_ident dst.au_updated_flag ]
             src.au_updated_flag))

(* A tracked mask entry's argument expressions are plain references to
   whatever program variables were in scope when the entry was established
   (the callable's own formals, seeded at entry; or a fresh local, added by
   a [fold]) -- never frozen the way [inv_snapshot] freezes an *open*
   instance's identity. If one of those variables is later reassigned, the
   entry becomes stale: it still syntactically names the same variable, but
   that variable no longer denotes the value the credit was actually about,
   and a later [Unfold]/[Call] could trivially, wrongly, syntactically
   match against it. Dropping any entry that mentions a just-written
   variable is always sound (never wrong to have less credit) and closes
   that gap -- e.g. `unfold i(x); y := x; foo(y, y)`, exploiting a stale
   `(i, [y])` entry to make a reentrant unfold of `i(x)` inside `foo` look
   like it's opening an unrelated, still-available instance. *)
let drop_mask_entries_mentioning (assigned : IdentSet.t) (mask : Callable.mask) :
    Callable.mask =
  List.filter mask ~f:(fun (_, args) ->
      List.for_all args ~f:(fun arg ->
          Set.is_empty (Set.inter (Expr.local_vars arg) assigned)))

(* Given a candidate mask-entry's argument prefix and the full argument list
   of the instance being opened, [None] means the candidate is too long to
   possibly cover the target (statically disjoint, no SMT needed); [Some
   conds] means it could cover it, with [conds] the (possibly empty) list of
   ground equalities that must hold at positions that aren't already
   syntactically [alpha_equal] -- this is the mask-membership half of the
   matching procedure. *)
let membership_conditions ~loc ~(candidate : Expr.t list) ~(target : Expr.t list) :
    Expr.t list option =
  let k = List.length candidate in
  if k > List.length target then None
  else
    let target_prefix = List.take target k in
    Some
      (List.filter_map (List.zip_exn candidate target_prefix) ~f:(fun (c, t) ->
           if Expr.alpha_equal c t then None else Some (Expr.mk_eq ~loc c t)))

(* Builds the formal -> actual-argument substitution for a call, accounting for
   trailing implicit ghost formals that a caller may omit at the call site
   (see [ImplicitInstantiation.infer_single_instantiation], where trailing
   implicit ghost formals may be omitted): if [call_args] has one entry per
   [formals] (including any implicit ones the caller chose to supply
   explicitly -- e.g. `acquire(l, r, b1)` in test/concurrent/lock/spin-lock.rav),
   zip directly against [formals]; if it has one entry per *non-implicit*
   formal only (the common case for an omitted trailing implicit), zip
   against those instead, leaving implicit formals unmapped. Any other length
   falls back to the empty map (no substitution), same as a genuine
   formal/actual mismatch -- callers already treat that as "leave unsubstituted"
   rather than aborting. Also returns the set of formal idents an actual was
   actually found for, so callers can recognize a formal that was genuinely
   never supplied (an omitted implicit) as opposed to one substituted to some
   caller expression. *)
let call_formal_actual_alignment (formals : Type.var_decl list) (call_args : Expr.t list)
    =
  let build assoc =
    let map =
      List.fold assoc
        ~init:(Map.empty (module QualIdent))
        ~f:(fun acc (formal, actual) ->
          Map.set acc ~key:(QualIdent.from_ident formal.Type.var_name) ~data:actual)
    in
    let resolved =
      List.map assoc ~f:(fun (formal, _) -> formal.Type.var_name)
      |> Set.of_list (module Ident)
    in
    (map, resolved)
  in
  if List.length call_args = List.length formals then
    build (List.zip_exn formals call_args)
  else
    let non_implicit_formals =
      List.filter formals ~f:(fun vd -> not vd.Type.var_implicit)
    in
    if List.length call_args = List.length non_implicit_formals then
      build (List.zip_exn non_implicit_formals call_args)
    else (Map.empty (module QualIdent), Set.empty (module Ident))

let call_formal_actual_map (formals : Type.var_decl list) (call_args : Expr.t list) =
  fst (call_formal_actual_alignment formals call_args)

(* A grant is discarded, rather than widened, if an omitted input has no actual. *)
let instantiate_grants ~strict (decl : Callable.call_decl) (call : Stmt.call_desc) grants
    =
  let formal_map, resolved =
    call_formal_actual_alignment decl.call_decl_formals call.call_args
  in
  let renaming, resolved =
    match
      List.fold2 decl.call_decl_returns call.call_lhs ~init:(formal_map, resolved)
        ~f:(fun (renaming, resolved) ret lhs ->
          ( Map.set renaming
              ~key:(QualIdent.from_ident ret.Type.var_name)
              ~data:(Expr.mk_var ~typ:ret.var_type lhs),
            Set.add resolved ret.var_name ))
    with
    | Ok aligned -> aligned
    | Unequal_lengths -> (formal_map, resolved)
  in
  List.filter_map grants ~f:(fun (head, args) ->
      if
        strict
        && List.exists args ~f:(fun arg ->
            not (Set.is_subset (Expr.local_vars arg) ~of_:resolved))
      then None
      else Some (head, List.map args ~f:(fun arg -> Expr.alpha_renaming arg renaming)))
  |> Callable.mask_canon

(* Number of explicit parameters of the declaration [qi]; positions past these
   in a mask entry are implicit parameters, on which two instances held at the
   same time agree if they agree on the explicit ones. *)
let explicit_arity (qi : QualIdent.t) ~(default : int) : (int, 'a) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let+ symbol = Rewriter.find qi in
  match Rewriter.Symbol.orig_symbol symbol with
  | CallDef { call_decl = { call_decl_formals; _ }; _ } -> List.length call_decl_formals
  | _ -> default

(* A call that omits a trailing implicit ghost formal (see
   [call_formal_actual_alignment] above) leaves the callee's own mask entry
   for it referring to the callee's own out-of-scope internal ident -- there
   is no caller expression to substitute in for it from the call site alone.
   Rather than leave that dangling (an out-of-scope ident must never reach
   the caller's own checks, syntactic or SMT-backed alike), try, in order:
   1. If the caller's ambient mask has a candidate entry for the same
      declaration, of the same (untruncated) arity, whose already-resolved
      prefix matches, and everything past that prefix falls entirely within
      the declaration's own implicit parameters (those after the `;`), then that
      candidate's remaining arguments are a sound stand-in for the omitted
      implicit (e.g. `Lk.acquire(lk)` against an ambient `lock_inv(lk, l)`
      unifies to exactly what `Lk.acquire(lk, l)` would give): [Lowering]'s
      `pred_valid$<qi>` lemma (generated for every [Pred]/[Invariant] with
      implicit parameters -- see its own doc comment) proves two
      simultaneously-held instances of [qi] agreeing on the explicit
      parameters must also agree on the implicit ones, checked or (for a
      [free] declaration) assumed either way -- so if there's more than one
      such candidate, any of them is as good as any other. An unresolved
      position within [qi]'s own explicit parameters gets no such guarantee
      (two candidates there could genuinely describe different, unrelated
      instances), so this is skipped whenever the resolved prefix doesn't
      reach past all of [qi]'s explicit parameters.
   2. Otherwise, truncate the entry down to just its resolved prefix -- the
      same coarsening [Masks.truncate_to_formal_expressible] already applies
      to an atomic spec's implicit formals: a position nothing at the call
      site can name is safely dropped rather than left dangling, at the cost
      of a coarser (but sound) requirement. This guarantees every entry this
      function returns is fully expressible at the call site, so the
      mask-availability check below can safely hand it to an SMT assert (or
      to [call_reentrancy_asserts]) without ever leaking a callee-internal
      ident into the caller's own scope. *)
let unify_omitted_implicit_mask ~(ambient_mask : Callable.mask)
    ~(formals : Type.var_decl list) ~(call_args : Expr.t list) (mask : Callable.mask) :
    (Callable.mask, 'a) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let renaming_map, resolved = call_formal_actual_alignment formals call_args in
  Rewriter.List.map mask ~f:(fun (head, args) ->
      let resolved_len =
        List.length
          (List.take_while args ~f:(fun arg ->
               Set.is_subset (Expr.local_vars arg) ~of_:resolved))
      in
      let substituted = List.map args ~f:(fun e -> Expr.alpha_renaming e renaming_map) in
      if resolved_len = List.length args then Rewriter.return (head, substituted)
      else
        let known_prefix = List.take substituted resolved_len in
        let truncated = (head, known_prefix) in
        let* n_formals =
          explicit_arity (Callable.mask_head_name head) ~default:(List.length args)
        in
        if resolved_len < n_formals then Rewriter.return truncated
        else
          let candidates =
            List.filter ambient_mask ~f:(fun (head', cand_args) ->
                Callable.equal_mask_head head' head
                && List.length cand_args = List.length args
                &&
                match
                  List.for_all2 known_prefix
                    (List.take cand_args resolved_len)
                    ~f:Expr.alpha_equal
                with
                | Ok b -> b
                | Unequal_lengths -> false)
          in
          match candidates with
          | (_, cand_args) :: _ -> Rewriter.return (head, cand_args)
          | [] -> Rewriter.return truncated)

(* [args] identifies an instance of [opened]'s declaration, possibly by a
   prefix of its arguments only. [Error ()] means every position is
   syntactically identical to [opened]'s: possibly the same instance, so
   reject. [Ok cond] is the disjunction of disequalities at the remaining
   positions -- discharging it proves the two instances are disjoint. The
   disequalities are against [opened]'s snapshot, not its [inv_args]: a
   variable in those may have been reassigned since the [unfold]. This is
   the disjointness half of the matching procedure. *)
let disjointness_condition ~loc (args : Expr.t list) (opened : invs) :
    (Expr.t, unit) Result.t =
  let open_args = List.take opened.inv_args (List.length args) in
  let diffs =
    List.filter_mapi (List.zip_exn args open_args) ~f:(fun i (a, b) ->
        if Expr.alpha_equal a b then None
        else
          Some
            (Expr.mk_not ~loc
               (Expr.mk_eq ~loc a (Expr.mk_tuple_lookup ~loc opened.inv_snapshot i))))
  in
  match diffs with [] -> Error () | _ -> Ok (Expr.mk_or ~loc diffs)

(* Finds which (if any) already-open instance of [inv_name] a [fold]
   supplying [use_args] closes: an exact syntactic ([alpha_equal]) match if
   one exists (unambiguous), else -- since multiple instances of the same
   declaration can be open at once -- the first candidate found, relying on
   the drift-detecting snapshot-equality assert below to reject a wrong
   guess. [None] means this is a fresh allocation, not a close. *)
let find_matching_open_inv (atomicity_state : atomicity_check) (inv_name : QualIdent.t)
    (use_args : Expr.t list) : invs option =
  let candidates =
    List.filter atomicity_state.invs_opened ~f:(fun inv ->
        QualIdent.equal inv.inv_name inv_name)
  in
  match
    List.find candidates ~f:(fun inv -> List.equal Expr.alpha_equal inv.inv_args use_args)
  with
  | Some inv -> Some inv
  | None -> List.hd candidates

let take_atomic_step ~loc (state : atomicity_check) : atomicity_check =
  if state.in_atomic_block then state
  else if List.is_empty state.au_opened && List.is_empty state.invs_opened then state
  else
    match state.atomic_step_taken with
    | false -> { state with atomic_step_taken = true }
    | true ->
        Error.verification_error ~code:Error.Atomicity loc
          "Attempting to take more than one atomic step with an open invariant or atomic \
           update"

let take_non_atomic_step ~loc (state : atomicity_check) : atomicity_check =
  if state.in_atomic_block then state
  else if List.is_empty state.au_opened && List.is_empty state.invs_opened then state
  else
    Error.verification_error ~code:Error.Atomicity loc
      "Cannot take a non-atomic step while an invariant or atomic update is open"

(* An extension statement is opaque here -- this pass has to run before the
   lowering that would reveal what it does, since e.g. a `cas` lowers to a read
   plus a conditional write yet is a single machine instruction. So the active
   extension declares the cost; see [Stmt.stmt_atomicity]. *)
let take_ext_step ~loc (atomicity : Stmt.stmt_atomicity) (state : atomicity_check) :
    atomicity_check =
  match atomicity with
  | NoStep -> state
  | AtomicStep -> take_atomic_step ~loc state
  | NonAtomicStep -> take_non_atomic_step ~loc state

(* Records a ghost update for every open instance, with the assignments that set their
   flags. *)
let mark_ghost_update ~loc (state : atomicity_check) : atomicity_check * Stmt.t list =
  let set_flag flag =
    Stmt.mk_assign ~loc [ Expr.to_qual_ident flag ] (Expr.mk_bool ~loc true)
  in
  ( {
      state with
      invs_opened =
        List.map state.invs_opened ~f:(fun inv -> { inv with inv_updated = true });
      au_opened = List.map state.au_opened ~f:(fun au -> { au with au_updated = true });
    },
    List.map state.invs_opened ~f:(fun inv -> set_flag inv.inv_updated_flag)
    @ List.map state.au_opened ~f:(fun au -> set_flag au.au_updated_flag) )

(* [into]'s open instances, each marked updated if it was updated in [from] too. *)
let join_ghost_updates ~(from : invs list) (into : invs list) : invs list =
  List.map into ~f:(fun inv ->
      let updated_in_from =
        List.exists from ~f:(fun other ->
            other.inv_updated
            && QualIdent.equal other.inv_name inv.inv_name
            && List.equal Expr.alpha_equal other.inv_args inv.inv_args)
      in
      { inv with inv_updated = inv.inv_updated || updated_in_from })

(* As [join_ghost_updates], for the open atomic update. *)
let join_au_updates ~(from : au_token list) (into : au_token list) : au_token list =
  List.map2_exn from into ~f:(fun src dst ->
      { dst with au_updated = dst.au_updated || src.au_updated })

(* A fresh ghost flag recording ghost updates, with its initialization to false. *)
let fresh_updated_flag ~loc (name : string) : (Expr.t * Stmt.t, 'a) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let flag_decl = Type.mk_var_decl ~ghost:true ~loc (Ident.fresh loc name) Type.bool in
  let+ () =
    Rewriter.introduce_symbol
      (Module.VarDef { var_decl = flag_decl; var_init = None; var_is_free = NotFree })
  in
  let flag = Expr.from_var_decl flag_decl in
  ( flag,
    Stmt.mk_assign ~loc ~is_init:true
      [ Expr.to_qual_ident flag ]
      (Expr.mk_bool ~loc false) )

(* The common oldest part of two paths' unfolded instances. *)
let common_preds_unfolded (l1 : unfolded_pred list) (l2 : unfolded_pred list) :
    unfolded_pred list =
  let same p1 p2 =
    QualIdent.equal p1.pred_name p2.pred_name
    && List.equal Expr.alpha_equal p1.pred_args p2.pred_args
  in
  let rec common acc = function
    | p1 :: l1, p2 :: l2 when same p1 p2 -> common (p1 :: acc) (l1, l2)
    | _ -> acc
  in
  common [] (List.rev l1, List.rev l2)

(* Maps the formals of [au]'s callable to the arguments it was opened with. *)
let au_renaming (callable_decl : Callable.call_decl) (au : au_token) :
    Expr.t Map.M(QualIdent).t =
  List.fold2_exn callable_decl.call_decl_formals
    (au.callable_args @ au.implicit_bound_vars)
    ~init:(Map.empty (module QualIdent))
    ~f:(fun acc_map formal_arg actual_arg ->
      Map.add_exn acc_map ~key:(QualIdent.from_ident formal_arg.var_name) ~data:actual_arg)

(* A logically atomic callee may abort, handing back its atomic precondition but
   keeping its ordinary one. Both preconditions are given up once before branching,
   sharing the selected frame with the call. The checking branch inhales only the
   atomic precondition before restoring the open AU and invariant instances: its
   internal existential witnesses may differ from those given up. The call itself
   does not give up either precondition again. If the ordinary precondition is pure, only an update or
   instance with a ghost update since it was opened is checked; any other is as
   closable as at its [openAU] or [unfold].
   Implicit arguments the call omits are bound first, as the call itself would bind them,
   and passed explicitly, so that the branch and the call agree on them. *)
let abort_check ~loc (call_decl : Callable.call_decl) (call_desc : Stmt.call_desc)
    (state : atomicity_check) :
    (Stmt.t list * Stmt.call_desc, atomicity_check) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let ordinary_precond =
    List.filter call_decl.call_decl_precond ~f:(fun spec -> not spec.spec_atomic)
  in
  let takes =
    List.exists ordinary_precond ~f:(fun spec ->
        not (Type.equal (Expr.to_type spec.spec_form |> Type.set_ghost false) Type.bool))
  in
  let checked =
    if takes then state.invs_opened
    else List.filter state.invs_opened ~f:(fun inv -> inv.inv_updated)
  in
  let checked_aus =
    if takes then state.au_opened
    else List.filter state.au_opened ~f:(fun au -> au.au_updated)
  in
  if List.is_empty checked && List.is_empty checked_aus then
    Rewriter.return ([], call_desc)
  else
    let fresh_ghost_var name typ =
      let var_decl = Type.mk_var_decl ~ghost:true ~loc (Ident.fresh loc name) typ in
      let+ () =
        Rewriter.introduce_symbol
          (Module.VarDef { var_decl; var_init = None; var_is_free = NotFree })
      in
      var_decl
    in
    let omitted =
      List.drop call_decl.call_decl_formals (List.length call_desc.call_args)
    in
    let* omitted_vars =
      Rewriter.List.map omitted ~f:(fun formal ->
          fresh_ghost_var formal.Type.var_name.ident_name formal.var_type)
    in
    let call_args = call_desc.call_args @ List.map omitted_vars ~f:Expr.from_var_decl in
    let renaming =
      List.fold2_exn call_decl.call_decl_formals call_args
        ~init:(Map.empty (module QualIdent))
        ~f:(fun renaming formal arg ->
          Map.set renaming ~key:(QualIdent.from_ident formal.Type.var_name) ~data:arg)
    in
    let instantiate (spec : Stmt.spec) = Expr.alpha_renaming spec.spec_form renaming in
    let bind_stmts =
      match omitted_vars with
      | [] -> []
      | _ :: _ ->
          let spec_error =
            match call_decl.call_decl_precond with
            | spec :: _ -> spec.spec_error
            | [] -> []
          in
          [
            Stmt.mk_bind ~loc
              (List.map omitted_vars ~f:(fun var -> QualIdent.from_ident var.var_name))
              (Stmt.mk_spec ~spec_error
                 (Expr.mk_and (List.map call_decl.call_decl_precond ~f:instantiate)));
          ]
    in
    let* callee = Rewriter.resolve call_desc.call_name in
    let exhale_preconditions atomic =
      List.filter_mapi call_decl.call_decl_precond ~f:(fun i spec ->
          Option.some_if
            (Bool.equal spec.spec_atomic atomic)
            (Stmt.mk_exhale_expr ~loc ?name:spec.spec_name ~spec_error:spec.spec_error
               ~spec_source:(callee, i) (instantiate spec)))
    in
    let exhale_stmts = exhale_preconditions false @ exhale_preconditions true in
    let inhale_atomic_stmts =
      List.filter_map call_decl.call_decl_precond ~f:(fun spec ->
          Option.some_if spec.spec_atomic (Stmt.mk_inhale_expr ~loc (instantiate spec)))
    in
    (* Each refolded instance is asserted, which lets a later refold find witnesses in
       it. *)
    let refold_stmts =
      List.concat_map state.preds_unfolded ~f:(fun pred ->
          let fold =
            Stmt.
              {
                stmt_desc =
                  Basic
                    (Use
                       {
                         use_kind = Fold;
                         use_name = pred.pred_name;
                         use_args = pred.pred_args;
                         use_witnesses_or_binds = pred.pred_witnesses;
                         use_spec_error =
                           [
                             Stmt.mk_const_spec_error
                               ( Error.Verification Error.Abortable_call,
                                 loc,
                                 "A predicate unfolded around this atomic call may not \
                                  be refoldable if the call aborts" );
                             Stmt.mk_const_spec_error
                               ( Error.RelatedLoc,
                                 pred.pred_loc,
                                 "This predicate may not be refoldable if the call aborts"
                               );
                           ];
                       });
                stmt_loc = loc;
              }
          in
          [
            fold;
            Stmt.mk_assert_expr ~loc
              (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var pred.pred_name) pred.pred_args);
          ])
    in
    let* abort_au_stmts =
      let+ stmts =
        Rewriter.List.map checked_aus ~f:(fun au ->
            let* symbol = Rewriter.find au.callable in
            let+ decl = Rewriter.Symbol.reify_callable_decl symbol in
            let renaming = au_renaming decl au in
            let exhales =
              List.filter_map decl.call_decl_precond ~f:(fun spec ->
                  if not spec.spec_atomic then None
                  else
                    let spec_error =
                      [
                        Stmt.mk_const_spec_error
                          ( Error.Verification Error.Abortable_call,
                            loc,
                            "The atomic update open around this atomic call may not be \
                             abortable if the call aborts" );
                        Stmt.mk_const_spec_error
                          ( Error.RelatedLoc,
                            au.au_loc,
                            "This atomic update may not be abortable if the call aborts"
                          );
                      ]
                    in
                    Some
                      (Stmt.mk_exhale_expr ~loc ~spec_error
                         (Expr.alpha_renaming spec.spec_form renaming)))
            in
            if takes then exhales
            else
              [
                Stmt.mk_cond ~loc (Some au.au_updated_flag)
                  (Stmt.mk_block_stmt ~loc exhales)
                  (Stmt.mk_block_stmt ~loc []);
              ])
      in
      List.concat stmts
    in
    let* fold_stmts =
      Rewriter.List.map checked ~f:(fun inv ->
          let* symbol = Rewriter.find inv.inv_name in
          let+ decl = Rewriter.Symbol.reify_callable_decl symbol in
          let arity =
            List.length decl.call_decl_formals + List.length decl.call_decl_returns
          in
          let use_args =
            List.init arity ~f:(fun i -> Expr.mk_tuple_lookup ~loc inv.inv_snapshot i)
          in
          let fold =
            Stmt.
              {
                stmt_desc =
                  Basic
                    (Use
                       {
                         use_kind = Fold;
                         use_name = inv.inv_name;
                         use_args;
                         use_witnesses_or_binds = [];
                         use_spec_error =
                           [
                             Stmt.mk_const_spec_error
                               ( Error.Verification Error.Abortable_call,
                                 loc,
                                 "An invariant open around this atomic call may not be \
                                  closable if the call aborts" );
                             Stmt.mk_const_spec_error
                               ( Error.RelatedLoc,
                                 inv.inv_loc,
                                 "This invariant may not be closable again if the call \
                                  aborts" );
                           ];
                       });
                stmt_loc = loc;
              }
          in
          if takes then fold
          else
            Stmt.mk_cond ~loc (Some inv.inv_updated_flag) fold
              (Stmt.mk_block_stmt ~loc []))
    in
    let+ abort = fresh_ghost_var "$abort" Type.bool in
    let abort_qi = QualIdent.from_ident abort.var_name in
    let branch =
      Stmt.mk_cond ~loc ~cond_if_assumes_false:true
        (Some (Expr.from_var_decl abort))
        (Stmt.mk_block_stmt ~loc
           (inhale_atomic_stmts @ refold_stmts @ abort_au_stmts @ fold_stmts
           @ [ Stmt.mk_assume_expr ~loc (Expr.mk_bool false) ]))
        (Stmt.mk_block_stmt ~loc [])
    in
    ( bind_stmts @ exhale_stmts @ [ Stmt.mk_havoc ~loc ~is_init:true abort_qi; branch ],
      { call_desc with call_args; call_precond_given = true } )

(* Returns the extra assert statements (reentrancy guard + membership proof)
   the caller must splice in immediately before the [Unfold] statement,
   together with the updated state. *)
let open_inv ~loc (inv_name, inv_args, inv_snapshot, inv_updated_flag) atomicity_state :
    atomicity_check * Stmt.t list =
  let atomicity_state =
    require_separation ~loc
      [ Callable.invariant_mask_entry inv_name inv_args ]
      atomicity_state
  in
  (* Reentrancy guard: this instance must be disjoint from every instance of
     the same declaration already open -- not decidable by name alone, since
     multiple instances of one declaration can be open simultaneously. *)
  let same_name_open =
    List.filter atomicity_state.invs_opened ~f:(fun inv ->
        QualIdent.equal inv.inv_name inv_name)
  in
  let reentrancy_asserts =
    List.map same_name_open ~f:(fun inv ->
        match disjointness_condition ~loc inv_args inv with
        | Error () ->
            Error.verification_error ~code:Error.Mask loc
              (Printf.sprintf
                 !"Invariant %{Ident} is already open"
                 (inv_name |> QualIdent.unqualify))
        | Ok cond ->
            let spec_error =
              let error =
                ( Error.Verification Error.Mask,
                  loc,
                  Printf.sprintf
                    !"Cannot unfold %{Ident}: this instance may be the same as one \
                      already open (arguments identifying the two instances are not \
                      provably distinct)"
                    (inv_name |> QualIdent.unqualify) )
              in
              [ Stmt.mk_const_spec_error error ]
            in
            Stmt.mk_assert_expr ~loc ~spec_error cond)
  in

  (* Mask consumption: find a currently-available entry that covers this
     instance. Prefer an exact syntactic match (no assert needed); otherwise
     take the first plausible candidate and require equality at whatever
     positions aren't already syntactically identical. *)
  let candidates =
    List.filter atomicity_state.mask ~f:(fun (head, _) ->
        Callable.equal_mask_head head (Callable.MaskHead.Invariant inv_name))
  in
  let scored =
    List.filter_map candidates ~f:(fun (head, args) ->
        match membership_conditions ~loc ~candidate:args ~target:inv_args with
        | None -> None
        | Some conds -> Some ((head, args), conds))
  in
  let chosen, membership_conds =
    match List.find scored ~f:(fun (_, conds) -> List.is_empty conds) with
    | Some (entry, conds) -> (entry, conds)
    | None -> (
        match scored with
        | [] ->
            Error.verification_error ~code:Error.Mask loc
              (Printf.sprintf
                 !"Invariant %{Ident} is not in the current mask"
                 (inv_name |> QualIdent.unqualify))
        | (entry, conds) :: _ -> (entry, conds))
  in
  let membership_asserts =
    List.map membership_conds ~f:(fun cond ->
        let spec_error =
          let error =
            ( Error.Verification Error.Mask,
              loc,
              Printf.sprintf
                !"Cannot unfold %{Ident}: the available mask entry's arguments are not \
                  provably equal to this instance's"
                (inv_name |> QualIdent.unqualify) )
          in
          [ Stmt.mk_const_spec_error error ]
        in
        Stmt.mk_assert_expr ~loc ~spec_error cond)
  in

  let mask =
    list_remove_first atomicity_state.mask ~f:(fun e ->
        Callable.compare_mask_entry e chosen = 0)
  in

  ( {
      atomicity_state with
      invs_opened =
        {
          inv_name;
          inv_args;
          inv_loc = loc;
          inv_snapshot;
          inv_consumed_mask_entry = chosen;
          inv_updated = false;
          inv_updated_flag;
        }
        :: atomicity_state.invs_opened;
      mask;
    },
    reentrancy_asserts @ membership_asserts )

(* [open_inv]'s reentrancy guard only fires for a direct [Unfold] -- but a
   call (lemma, ordinary proc, or atomic proc alike) whose own mask
   requirement includes an entry for some declaration is, from this
   caller's perspective, indistinguishable from that declaration being
   unfolded right here: the callee is opaque, and its contract already
   says it may need to open exactly this. So if the caller currently has
   some *other* instance of the same declaration open (in [invs_opened]),
   the call needs the same disjointness obligation [open_inv] would
   demand of a direct [Unfold] -- otherwise a lemma call nested inside an
   open invariant's region can silently reopen the same real instance
   under a different name, e.g. `unfold i(x); foo(y)` with `foo` itself
   unfolding its own `i(y)` formal, and nothing ever requiring `x != y`.
   Applied uniformly to every call kind by being computed once in the
   shared [Call] handling, not per-branch. *)
let call_reentrancy_asserts ~loc (atomicity_state : atomicity_check)
    (required : Callable.mask) : Stmt.t list =
  let required =
    match atomicity_state.namespace_draft with
    | None -> required
    | Some _ ->
        List.filter required ~f:(fun (head, _) ->
            match head with
            | Callable.MaskHead.Invariant _ -> true
            | Dependencies _ -> false)
  in
  List.concat_map required ~f:(fun (head, args) ->
      let qi = Callable.invariant_mask_name ~loc head in
      let same_name_open =
        List.filter atomicity_state.invs_opened ~f:(fun inv ->
            QualIdent.equal inv.inv_name qi)
      in
      (* [args] may be a coarse prefix (e.g. a truncated implicit); an empty
         or matching prefix is rejected as possibly the same instance. *)
      (* The instance must be folded before the call, as before a return: report it as
         a missing fold, pointing back at the [unfold]. *)
      List.map same_name_open ~f:(fun inv ->
          let unfolded =
            ( Error.RelatedLoc,
              inv.inv_loc,
              Printf.sprintf "%s was unfolded here" (inv_to_string inv) )
          in
          match disjointness_condition ~loc args inv with
          | Error () ->
              Error.fail_with
                [
                  ( Error.Verification Error.Unclosed,
                    loc,
                    Printf.sprintf "Missing fold for unfolded invariant %s"
                      (inv_to_string inv) );
                  unfolded;
                ]
          | Ok cond ->
              let spec_error =
                let error =
                  ( Error.Verification Error.Unclosed,
                    loc,
                    Printf.sprintf
                      "Missing fold for unfolded invariant %s, which the callee may need \
                       (the arguments identifying the two instances are not provably \
                       distinct)"
                      (inv_to_string inv) )
                in
                [ Stmt.mk_const_spec_error error; Stmt.mk_const_spec_error unfolded ]
              in
              Stmt.mk_assert_expr ~loc ~spec_error cond))

(* [matching_open_inv] is [find_matching_open_inv]'s result, computed by the
   caller (it's also needed there for the drift-detecting snapshot-equality
   assert). [None] means this is a fresh allocation: folding a fresh
   instance never *checks* the mask, matching Iris's [inv_alloc] placing no
   precondition on the ambient mask -- but it now *does* grant credit for
   the freshly-allocated instance going forward, path-sensitively, through
   the rest of this callable's own control flow: this is sound because mask
   credit tracks per-thread reentrancy, not a shared exclusive budget -- the
   persistent invariant-existence fact [inv_alloc] produces is exactly what's
   being tracked, and duplicating it forward is the same reasoning Iris's Par
   rule uses for parallel composition. This is what lets a callable that
   allocates and
   immediately reopens its own fresh instance need nothing external for it,
   without granting any exemption from the reentrancy guard in [open_inv]
   above (an [unfold] of this same instance while it's still open is still
   rejected there, unaffected by any of this). *)
let close_inv ~(inv_name : QualIdent.t) ~(inv_args : Expr.t list)
    (matching_open_inv : invs option) atomicity_state : atomicity_check =
  match matching_open_inv with
  | None ->
      {
        atomicity_state with
        mask =
          Callable.mask_union atomicity_state.mask
            [ Callable.invariant_mask_entry inv_name inv_args ];
      }
  | Some inv ->
      let invs_opened =
        list_remove_first atomicity_state.invs_opened ~f:(fun i ->
            QualIdent.equal i.inv_name inv.inv_name
            && List.equal Expr.alpha_equal i.inv_args inv.inv_args)
      in
      let mask =
        Callable.mask_union atomicity_state.mask [ inv.inv_consumed_mask_entry ]
      in
      if List.is_empty invs_opened && List.is_empty atomicity_state.au_opened then
        {
          atomicity_state with
          invs_opened;
          mask;
          atomic_step_taken = false;
          preds_unfolded = [];
        }
      else { atomicity_state with invs_opened; mask }

let open_au ~loc ~source_token
    (token, callable, callable_args, implicit_bound_vars, au_updated_flag) atomicity_state
    : atomicity_check =
  if List.exists atomicity_state.au_opened ~f:(fun au -> Expr.alpha_equal au.token token)
  then
    Error.verification_error ~code:Error.Atomic_update loc
      (Printf.sprintf
         !"Atomic token %{String} is already open"
         (Expr.to_source_string source_token))
  else if not (List.is_empty atomicity_state.au_opened) then
    (* At most one atomic update may be open at a time. A once-open AU's own
       [α] is licensed by a genuine mask-shrink (or, for a proc's own token,
       by its caller's external obligation); a second, simultaneously-open AU
       has no such license of its own and would let openAU mint an
       independent, unconstrained copy of whatever its atomic precondition
       says -- e.g. two coexisting full shares of the same exclusive
       resource. Closing the current AU first (commitAU/abortAU) and only
       then opening the next is always sufficient: view shifts are purely
       logical, so nothing can interleave between the close and the next
       open, and the next open still has to honestly justify its own atomic
       precondition against whatever is actually held at that point. *)
    Error.verification_error ~code:Error.Atomic_update loc
      (Printf.sprintf
         !"Cannot open atomic token %{String} while another atomic update is still open; \
           commit or abort it first"
         (Expr.to_source_string source_token))
  else
    {
      atomicity_state with
      au_opened =
        {
          token;
          source_token;
          callable;
          callable_args;
          implicit_bound_vars;
          au_loc = loc;
          au_updated = false;
          au_updated_flag;
        }
        :: atomicity_state.au_opened;
    }

let close_au ~loc token atomicity_state : atomicity_check =
  if
    not
      (List.exists atomicity_state.au_opened ~f:(fun au ->
           Expr.alpha_equal au.token token))
  then
    Error.verification_error ~code:Error.Atomic_update loc
      (Printf.sprintf
         !"Atomic token %{String} is not open (nothing to close)"
         (Expr.to_source_string token))
  else
    let au_opened =
      List.filter atomicity_state.au_opened ~f:(fun au ->
          not (Expr.alpha_equal au.token token))
    in

    if List.is_empty au_opened && List.is_empty atomicity_state.invs_opened then
      { atomicity_state with au_opened; atomic_step_taken = false; preds_unfolded = [] }
    else { atomicity_state with au_opened }

(* Whether [stmt] cannot take a resource that closing an open invariant needs, nor
   replace one by a weaker one. A call is classified where it is checked. *)
let keeps_closable (stmt : Stmt.t) : bool =
  match stmt.stmt_desc with
  | Basic
      (VarDef _ | New _ | Assign _ | Bind _ | Havoc _ | FieldRead _ | Return _ | Call _)
    ->
      true
  | Basic (Spec (kind, _)) -> not (Poly.equal kind Stmt.Exhale)
  | Basic (Use { use_kind = Unfold; _ }) -> true
  | Basic (AUAction { auaction_kind = BindAU _ | OpenAU _; _ }) -> true
  | Basic (Use { use_kind = Fold; _ } | AUAction _ | Fpu _ | FieldWrite _ | BasicStmtExt _)
  | StmtExt _ ->
      false
  | Block _ | Cond _ | Loop _ -> true

let rewrite_au_cmnds (stmt : Stmt.t) : (Stmt.t, atomicity_check) Rewriter.t_ext =
  let open Rewriter.Syntax in
  (* Every open instance is marked updated before a statement that may make it less
     closable (see [keeps_closable]). *)
  let rec rewrite_au_cmnds (stmt : Stmt.t) : (Stmt.t, atomicity_check) Rewriter.t_ext =
    let loc = stmt.stmt_loc in
    let* atomicity_state = Rewriter.current_user_state in
    let atomicity_state, update_flag_stmts =
      if keeps_closable stmt then (atomicity_state, [])
      else mark_ghost_update ~loc atomicity_state
    in
    let* () = Rewriter.set_user_state atomicity_state in
    let+ stmt = rewrite_au_cmnd stmt in
    match update_flag_stmts with
    | [] -> stmt
    | _ :: _ -> Stmt.mk_block_stmt ~loc (stmt :: update_flag_stmts)
  and rewrite_au_cmnd (stmt : Stmt.t) : (Stmt.t, atomicity_check) Rewriter.t_ext =
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    let* curr_callable_name = Rewriter.current_scope_id in

    let callable_info call_ident =
      let* symbol = Rewriter.find call_ident in
      let+ callable = Rewriter.Symbol.reify_callable_decl symbol in

      let concrete_args =
        List.filter callable.call_decl_formals ~f:(fun var_decl ->
            not var_decl.var_implicit)
      in
      let implicit_args =
        List.filter callable.call_decl_formals ~f:(fun var_decl -> var_decl.var_implicit)
      in
      (callable, concrete_args, implicit_args)
    in

    let* () =
      Rewriter.Logs.debug (fun printers m ->
          m "Elaboration.rewrite_au_cmnds: curr_callable_name: %a; stmt=%a" QualIdent.pr
            curr_callable_name printers.pr_stmt stmt)
    in

    let loc = stmt.stmt_loc in

    let* atomicity_state = Rewriter.current_user_state in

    (* Assigned-variable-drops mask entries mentioning them; see
       [drop_mask_entries_mentioning]'s doc comment. The arguments are the
       (possibly ghost) variables this statement writes to. *)
    let drop_stale_idents ~(idents : Ident.t list) (state : atomicity_check) :
        atomicity_check =
      let assigned = Set.of_list (module Ident) idents in
      let mentions_assigned pred =
        List.exists
          (pred.pred_args @ List.map pred.pred_witnesses ~f:snd)
          ~f:(fun arg -> not (Set.is_empty (Set.inter (Expr.local_vars arg) assigned)))
      in
      {
        state with
        mask = drop_mask_entries_mentioning assigned state.mask;
        preds_unfolded =
          List.filter state.preds_unfolded ~f:(fun pred -> not (mentions_assigned pred));
      }
    in
    let drop_stale ~(qis : QualIdent.t list) (state : atomicity_check) : atomicity_check =
      drop_stale_idents ~idents:(List.map qis ~f:QualIdent.unqualify) state
    in

    let prior_au_bindings = atomicity_state.au_bindings in
    let* atomicity_state =
      let written =
        match stmt.stmt_desc with
        | Basic (AUAction { auaction_kind = OpenAU opened }) ->
            List.concat_map opened.lhs ~f:(fun expr -> Set.to_list (Expr.local_vars expr))
        | Basic (VarDef _ | AUAction _) -> []
        | Basic _ -> Stmt.stmt_local_vars_modified stmt
        | Block _ | Cond _ | Loop _ | StmtExt _ -> []
      in
      let assigned = Set.of_list (module Ident) written in
      let* () =
        if
          List.exists atomicity_state.au_opened ~f:(fun au ->
              not (Set.is_empty (Set.inter (Expr.local_vars au.token) assigned)))
        then
          Error.verification_error ~code:Error.Atomic_update loc
            "An open atomic token cannot be reassigned before commitAU or abortAU"
        else Rewriter.return ()
      in
      let state =
        {
          atomicity_state with
          au_bindings = Set.diff atomicity_state.au_bindings assigned;
        }
      in
      let* () = Rewriter.set_user_state state in
      Rewriter.return state
    in

    let normalize_token state token =
      match token with
      | App (Var qi, [], _) when Set.mem state.au_bindings (QualIdent.unqualify qi) ->
          let name =
            QualIdent.from_ident
              (ProgUtils.callable_au_token_ident ~loc
                 (QualIdent.unqualify curr_callable_name))
          in
          let* symbol = Rewriter.find name in
          begin match Rewriter.Symbol.orig_symbol symbol with
          | VarDef _ ->
              let+ token = Rewriter.Symbol.reify_var_decl symbol in
              Expr.from_var_decl token
          | _ -> Error.internal_error loc "expected an atomic token variable"
          end
      | _ -> Rewriter.return token
    in

    match stmt.stmt_desc with
    | Basic (New new_desc) ->
        let* new_lhs =
          let* symbol = Rewriter.find new_desc.new_lhs in
          match Rewriter.Symbol.orig_symbol symbol with
          | VarDef v -> Rewriter.return v
          | _ -> Error.internal_error stmt.stmt_loc "expected a var_def"
        in

        let atomicity_state = drop_stale ~qis:[ new_desc.new_lhs ] atomicity_state in
        if new_lhs.var_decl.var_ghost then
          let* _ = Rewriter.set_user_state atomicity_state in
          Rewriter.return stmt
        else
          let atomicity_state = take_atomic_step ~loc atomicity_state in
          let* _ = Rewriter.set_user_state atomicity_state in
          Rewriter.return stmt
    | Basic (Assign assign_desc) ->
        let atomicity_state = drop_stale ~qis:assign_desc.assign_lhs atomicity_state in
        let atomicity_state =
          match (assign_desc.assign_lhs, assign_desc.assign_rhs) with
          | [ lhs ], App (Var rhs, [], _)
            when Set.mem prior_au_bindings (QualIdent.unqualify rhs) ->
              {
                atomicity_state with
                au_bindings =
                  Set.add atomicity_state.au_bindings (QualIdent.unqualify lhs);
              }
          | _ -> atomicity_state
        in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (Bind bind_desc) ->
        let atomicity_state = drop_stale ~qis:bind_desc.bind_lhs atomicity_state in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (FieldRead field_read_desc) -> (
        let* symbol = Rewriter.find field_read_desc.field_read_lhs in
        let atomicity_state =
          drop_stale ~qis:[ field_read_desc.field_read_lhs ] atomicity_state
        in
        match Rewriter.Symbol.orig_symbol symbol with
        | VarDef v ->
            if v.var_decl.var_ghost then
              let* _ = Rewriter.set_user_state atomicity_state in
              Rewriter.return stmt
            else
              let atomicity_state = take_atomic_step ~loc atomicity_state in
              let* _ = Rewriter.set_user_state atomicity_state in
              Rewriter.return stmt
        | _ -> Error.internal_error stmt.stmt_loc "expected a var_def")
    | Basic (FieldWrite field_write_desc) -> (
        let* symbol = Rewriter.find field_write_desc.field_write_field in
        match Rewriter.Symbol.orig_symbol symbol with
        | FieldDef fld ->
            if fld.field_is_ghost then Rewriter.return stmt
            else
              let atomicity_state = take_atomic_step ~loc atomicity_state in
              let* _ = Rewriter.set_user_state atomicity_state in
              Rewriter.return stmt
        | _ -> Error.internal_error stmt.stmt_loc "expected a field_def")
    | Basic (Fpu _) -> Rewriter.return stmt
    | Basic (Havoc hvc) ->
        let atomicity_state = drop_stale ~qis:[ hvc.havoc_var ] atomicity_state in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (Call call_desc) ->
        let* symbol = Rewriter.find call_desc.call_name in
        let* call_decl =
          match Rewriter.Symbol.orig_symbol symbol with
          | CallDef _ -> Rewriter.Symbol.reify_callable_decl symbol
          | _ -> Error.internal_error stmt.stmt_loc "expected a call_def"
        in

        (* The callee's mask entries are expressed in terms of its own
           formals; substitute the actual call arguments before comparing
           against the caller's (locals-relative) mask.

           Substitution is only attempted when the callee's mask actually
           has a non-empty (fine-grained) entry -- the overwhelming common
           case is every entry being the coarse [], which needs no
           substitution at all, and formal/actual alignment (concrete vs.
           `implicit`, which callers may or may not supply explicitly) isn't
           always simply "drop the implicit formals" -- see e.g.
           `acquire(l, r, b1)` explicitly supplying implicit formals in
           test/concurrent/lock/spin-lock.rav. [unify_omitted_implicit_mask]
           below handles a length mismatch (including whatever it can't
           itself resolve) rather than aborting, so a genuine alignment gap
           surfaces as an ordinary (safe) mask-unavailability check instead
           of crashing the compiler. *)
        let* callee_mask, grants, atomicity_state =
          match atomicity_state.namespace_draft with
          | None ->
              let* required =
                Masks.resolve_mask (Option.value_exn call_decl.call_decl_needs_mask)
              in
              let+ grants =
                Masks.resolve_mask
                  (Option.value call_decl.call_decl_grants_mask ~default:[])
              in
              (required, grants, atomicity_state)
          | Some draft ->
              let* summary = NamespaceInference.find_callable draft call_desc.call_name in
              let summary =
                match summary with
                | Some summary -> summary
                | None ->
                    Error.internal_error loc "Missing draft namespace summary for callee"
              in
              let+ callee = Rewriter.resolve call_desc.call_name in
              ( summary.requires,
                summary.grants,
                {
                  atomicity_state with
                  separation =
                    union_separation atomicity_state.separation summary.separation;
                  callees = Set.add atomicity_state.callees callee;
                } )
        in
        let needs_substitution =
          List.exists callee_mask ~f:(fun (_, args) -> not (List.is_empty args))
        in
        let* required_at_call_site =
          if not needs_substitution then Rewriter.return callee_mask
          else
            unify_omitted_implicit_mask ~ambient_mask:atomicity_state.mask
              ~formals:call_decl.call_decl_formals ~call_args:call_desc.call_args
              callee_mask
        in
        (* A call doesn't remove anything from the mask -- it's a pure query,
           "does the caller already have room for what the callee needs" --
           so unlike [open_inv]/[Unfold], there's nothing to commit to if the
           cheap syntactic check below doesn't immediately settle it. Try
           that fast path first (covers the overwhelming common case, and
           the coarse-[] entries in particular, for free); only fall back to
           an SMT assert per still-unresolved required entry, disjoining
           the positional equalities of every same-declaration ambient
           candidate that covers the required entry. Zero
           candidates collapses to the empty disjunction, i.e. `assert
           false` -- proving the call site is semantically unreachable is
           strictly more informative than the outright compiler rejection
           this replaces, and no worse when it isn't: the assert just fails
           like any other. [required_at_call_site] is guaranteed free of any
           callee-internal ident by [unify_omitted_implicit_mask] above, so
           every position here is safe to name in a caller-side assert. *)
        let* required_with_arity =
          Rewriter.List.map required_at_call_site ~f:(fun (head, args) ->
              let qi = Callable.mask_head_name head in
              let+ n_explicit = explicit_arity qi ~default:(List.length args) in
              (head, args, n_explicit))
        in
        let availability_asserts =
          List.filter_map required_with_arity
            ~f:(fun (required_head, target_args, n_explicit) ->
              let qi = Callable.mask_head_name required_head in
              (* A candidate longer than the requirement covers it only if the
                 requirement already fixes every explicit parameter: the extra
                 positions are then implicit parameters, on which instances
                 held at the same time agree. *)
              let covering_conditions cand_args =
                let k = List.length target_args in
                let cand_args =
                  if k >= n_explicit then List.take cand_args k else cand_args
                in
                membership_conditions ~loc ~candidate:cand_args ~target:target_args
              in
              let candidates =
                List.filter_map atomicity_state.mask ~f:(fun (head, cand_args) ->
                    if Callable.equal_mask_head head required_head then
                      covering_conditions cand_args
                    else None)
              in
              if List.exists candidates ~f:List.is_empty then None
              else
                let disjuncts = List.map candidates ~f:(Expr.mk_and ~loc) in
                let cond = Expr.mk_or ~loc disjuncts in
                let call_id = call_desc.call_name |> QualIdent.unqualify in
                let error =
                  ( Error.Verification Error.Mask,
                    loc,
                    Printf.sprintf
                      !"Cannot call %{Ident}. The invariant %{Ident} required by \
                        %{Ident} is not available in the current mask"
                      call_id (qi |> QualIdent.unqualify) call_id )
                in
                Some
                  (Stmt.mk_assert_expr ~loc
                     ~spec_error:[ Stmt.mk_const_spec_error error ]
                     cond))
        in
        let atomicity_state =
          require_separation ~loc required_at_call_site atomicity_state
        in
        let reentrancy_asserts =
          call_reentrancy_asserts ~loc atomicity_state required_at_call_site
        in
        let* is_call_lhs_ghost =
          Rewriter.List.for_all call_desc.call_lhs ~f:(fun qual_iden ->
              let* symbol = Rewriter.find qual_iden in
              match Rewriter.Symbol.orig_symbol symbol with
              | VarDef v -> Rewriter.return v.var_decl.var_ghost
              | _ -> Error.internal_error stmt.stmt_loc "expected a var_def")
        in

        (* Drop any existing entry that mentions one of this call's own
           lhs-bound variables *before* computing grants-set credit below
           -- the call is about to overwrite those variables, so any
           pre-existing mask entry mentioning them is now stale (see
           [drop_mask_entries_mentioning]), while any *new* grants-set
           entry computed below legitimately describes their post-call
           value and must not be dropped by this same step. *)
        let atomicity_state = drop_stale ~qis:call_desc.call_lhs atomicity_state in

        (* Grants-set credit: does calling this callee hand *this* caller
           local mask credit, the same way a local [fold] would? (See
           [Callable.call_decl_grants_mask]'s doc comment.) Applied
           uniformly regardless of which branch below is taken --
           including logical function and lemma calls, which otherwise
           never touch [atomicity_state] at all,
           since a lemma can still fold a fresh invariant and hand its
           credit onward exactly like a proc can. Substituted through both
           the actual call arguments (the callee's own formals) and the
           call's lhs bindings (the callee's own return variables), since
           a grants-set entry -- unlike [call_decl_needs_mask] -- can be
           expressed via either. *)
        let* atomicity_state =
          match grants with
          | [] -> Rewriter.return atomicity_state
          | grants ->
              let needs_substitution =
                List.exists grants ~f:(fun (_, args) -> not (List.is_empty args))
              in
              if not needs_substitution then
                Rewriter.return
                  {
                    atomicity_state with
                    mask = Callable.mask_union atomicity_state.mask grants;
                  }
              else
                let credited =
                  instantiate_grants
                    ~strict:(Option.is_some atomicity_state.namespace_draft)
                    call_decl call_desc grants
                in
                Rewriter.return
                  {
                    atomicity_state with
                    mask = Callable.mask_union atomicity_state.mask credited;
                  }
        in

        if call_decl.call_decl_physical_atomic && not call_desc.call_is_spawn then
          let atomicity_state = take_atomic_step ~loc atomicity_state in
          let* _ = Rewriter.set_user_state atomicity_state in
          Rewriter.return
            (Stmt.mk_block_stmt ~loc
               (availability_asserts @ reentrancy_asserts @ [ stmt ]))
        else if
          Poly.(call_decl.call_decl_kind = Lemma)
          || Poly.(call_decl.call_decl_kind = Func)
             && is_call_lhs_ghost
             && not (List.is_empty call_desc.call_lhs)
        then
          let atomicity_state, flag_stmts = mark_ghost_update ~loc atomicity_state in
          let* _ = Rewriter.set_user_state atomicity_state in
          Rewriter.return
            (Stmt.mk_block_stmt ~loc
               (availability_asserts @ reentrancy_asserts @ [ stmt ] @ flag_stmts))
        else if Callable.is_atomic call_decl && not call_desc.call_is_spawn then
          let* abort_stmts, call_desc =
            abort_check ~loc call_decl call_desc atomicity_state
          in
          let stmt = { stmt with stmt_desc = Basic (Call call_desc) } in
          let atomicity_state = take_atomic_step ~loc atomicity_state in
          let* _ = Rewriter.set_user_state atomicity_state in
          Rewriter.return
            (Stmt.mk_block_stmt ~loc
               (availability_asserts @ reentrancy_asserts @ abort_stmts @ [ stmt ]))
        else
          let atomicity_state, flag_stmts =
            (if Callable.is_atomic call_decl && not call_decl.call_decl_physical_atomic
             then take_atomic_step ~loc atomicity_state
             else take_non_atomic_step ~loc atomicity_state)
            |> mark_ghost_update ~loc
          in
          let* _ = Rewriter.set_user_state atomicity_state in
          Rewriter.return
            (Stmt.mk_block_stmt ~loc
               (availability_asserts @ reentrancy_asserts @ [ stmt ] @ flag_stmts))
    | Basic (BasicStmtExt (stmt_ext, args)) ->
        let* ext_hooks = Rewriter.current_ext_hooks in
        let atomicity_state =
          drop_stale_idents
            ~idents:(ext_hooks.basic_stmt_ext_local_vars_modified stmt_ext args)
            atomicity_state
        in
        let atomicity_state =
          take_ext_step ~loc (ext_hooks.stmt_ext_atomicity stmt_ext) atomicity_state
        in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (Return return_expr) ->
        let atomicity_state = take_atomic_step ~loc atomicity_state in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (Use use_desc) -> (
        let* use_name, symbol = Rewriter.resolve_and_find use_desc.use_name in
        let use_desc = { use_desc with use_name } in
        let stmt = { stmt with stmt_desc = Basic (Use use_desc) } in
        match Rewriter.Symbol.orig_symbol symbol with
        | CallDef _ -> (
            let* decl = Rewriter.Symbol.reify_callable_decl symbol in
            match decl.call_decl_kind with
            | Pred -> (
                let tracking =
                  not
                    (List.is_empty atomicity_state.au_opened
                    && List.is_empty atomicity_state.invs_opened)
                in
                match use_desc.use_kind with
                | Unfold when tracking ->
                    let* pred_witnesses =
                      Rewriter.List.map use_desc.use_witnesses_or_binds
                        ~f:(fun (local, exist) ->
                          let+ local_decl =
                            let* symbol = Rewriter.find (QualIdent.from_ident local) in
                            Rewriter.Symbol.reify_var_decl symbol
                          in
                          (Expr.to_ident exist, Expr.from_var_decl local_decl))
                    in
                    let unfolded =
                      {
                        pred_name = use_desc.use_name;
                        pred_args = use_desc.use_args;
                        pred_witnesses;
                        pred_loc = loc;
                      }
                    in
                    let* _ =
                      Rewriter.set_user_state
                        {
                          atomicity_state with
                          preds_unfolded = unfolded :: atomicity_state.preds_unfolded;
                        }
                    in
                    Rewriter.return stmt
                | Fold ->
                    let preds_unfolded =
                      list_remove_first atomicity_state.preds_unfolded ~f:(fun pred ->
                          QualIdent.equal pred.pred_name use_desc.use_name
                          && List.equal Expr.alpha_equal pred.pred_args use_desc.use_args)
                    in
                    let* _ =
                      Rewriter.set_user_state { atomicity_state with preds_unfolded }
                    in
                    Rewriter.return stmt
                | Unfold -> Rewriter.return stmt)
            | Invariant -> (
                let all_params = decl.call_decl_formals @ decl.call_decl_returns in
                match use_desc.use_kind with
                | Unfold ->
                    (* Implicit arguments left out here are bound to fresh
                       ghost variables, so that the snapshot covers them. *)
                    let omitted = List.drop all_params (List.length use_desc.use_args) in
                    let* omitted_vars =
                      Rewriter.List.map omitted ~f:(fun vd ->
                          let var_decl =
                            Type.mk_var_decl ~ghost:true ~loc
                              (Ident.fresh loc vd.Type.var_name.ident_name)
                              vd.var_type
                          in
                          let+ () =
                            Rewriter.introduce_symbol
                              (Module.VarDef
                                 { var_decl; var_init = None; var_is_free = NotFree })
                          in
                          var_decl)
                    in
                    let full_args =
                      use_desc.use_args @ List.map omitted_vars ~f:Expr.from_var_decl
                    in
                    let bind_stmts =
                      match omitted_vars with
                      | [] -> []
                      | _ :: _ ->
                          let spec_error =
                            let error =
                              ( Error.Verification Error.Unfold,
                                loc,
                                "Failed to unfold predicate. The predicate may not hold \
                                 at this point" )
                            in
                            [ Stmt.mk_const_spec_error error ]
                          in
                          [
                            Stmt.mk_bind ~loc
                              (List.map omitted_vars ~f:(fun vd ->
                                   QualIdent.from_ident vd.var_name))
                              (Stmt.mk_spec ~spec_error
                                 (Expr.mk_app ~loc ~typ:Type.bool
                                    (Expr.Var use_desc.use_name) full_args));
                          ]
                    in
                    (* See [invs.inv_snapshot]. Skip for 0-arity invariants
                       (e.g. [inv inv1() { ... }]): only one instance is
                       possible, so there's no identity to freeze. *)
                    let* snap_expr, snap_stmts =
                      match full_args with
                      | [] -> Rewriter.return (Expr.mk_bool ~loc true, [])
                      | _ :: _ ->
                          let snap_ident =
                            Ident.fresh loc
                              ("$inv_snapshot_"
                              ^ Ident.to_string (QualIdent.unqualify use_desc.use_name))
                          in
                          let snap_type =
                            Type.mk_prod loc (List.map full_args ~f:Expr.to_type)
                          in
                          let snap_var_decl =
                            Type.mk_var_decl ~ghost:true ~loc snap_ident snap_type
                          in
                          let+ () =
                            Rewriter.introduce_symbol
                              (Module.VarDef
                                 {
                                   var_decl = snap_var_decl;
                                   var_init = None;
                                   var_is_free = NotFree;
                                 })
                          in
                          let snap_expr =
                            Expr.mk_var ~typ:snap_type (QualIdent.from_ident snap_ident)
                          in
                          let snap_assign_stmt =
                            Stmt.mk_assign ~loc ~is_init:true
                              [ QualIdent.from_ident snap_ident ]
                              (Expr.mk_tuple ~loc full_args)
                          in
                          (snap_expr, [ snap_assign_stmt ])
                    in
                    let* flag, flag_init =
                      fresh_updated_flag ~loc
                        ("$inv_updated_"
                        ^ Ident.to_string (QualIdent.unqualify use_desc.use_name))
                    in
                    let flag_stmts = [ flag_init ] in
                    let atomicity_state, open_asserts =
                      open_inv ~loc
                        (use_desc.use_name, use_desc.use_args, snap_expr, flag)
                        atomicity_state
                    in
                    let* _ = Rewriter.set_user_state atomicity_state in
                    let stmt =
                      {
                        stmt with
                        stmt_desc = Basic (Use { use_desc with use_args = full_args });
                      }
                    in
                    (* The snapshot follows the unfold, which lowering then knows it
                       copies the instance's arguments. *)
                    Rewriter.return
                      (Stmt.mk_block_stmt ~loc
                         (bind_stmts @ open_asserts @ flag_stmts @ [ stmt ] @ snap_stmts))
                | Fold -> (
                    (* Multiple instances of the same declaration can be open
                       at once, so this needs to identify which one; see
                       [find_matching_open_inv]. Present means this fold
                       closes it and must match its snapshot; absent means
                       this is a fresh allocation. *)
                    let matching_open_inv =
                      find_matching_open_inv atomicity_state use_desc.use_name
                        use_desc.use_args
                    in
                    let atomicity_state =
                      close_inv ~inv_name:use_desc.use_name ~inv_args:use_desc.use_args
                        matching_open_inv atomicity_state
                    in
                    let* _ = Rewriter.set_user_state atomicity_state in
                    match (matching_open_inv, all_params) with
                    | None, _ | _, [] ->
                        (* Fresh allocation, or 0-arity (no snapshot exists). *)
                        Rewriter.return stmt
                    | Some inv, _ :: _ ->
                        (* Implicit arguments left out here are restored from
                           the snapshot: closing must not change them. *)
                        let n_written = List.length use_desc.use_args in
                        let full_args =
                          use_desc.use_args
                          @ List.mapi (List.drop all_params n_written) ~f:(fun i _ ->
                              Expr.mk_tuple_lookup ~loc inv.inv_snapshot (n_written + i))
                        in
                        let spec_error =
                          let inv_id = use_desc.use_name |> QualIdent.unqualify in
                          let msg =
                            if List.is_empty decl.call_decl_returns then
                              Printf.sprintf
                                !"Cannot fold %{Ident}: its arguments no longer match \
                                  the instance that was opened by the corresponding \
                                  unfold (a variable used to identify the instance may \
                                  have been reassigned in between)"
                                inv_id
                            else
                              Printf.sprintf
                                !"Cannot fold %{Ident}: its arguments may differ from \
                                  those of the instance opened by the corresponding \
                                  unfold. Either a variable used as an argument was \
                                  reassigned in between, or an implicit argument \
                                  changed, which an invariant does not allow"
                                inv_id
                          in
                          let error =
                            (Error.Verification Error.Invariant_arguments, loc, msg)
                          in
                          [ Stmt.mk_const_spec_error error ]
                        in
                        let assert_stmt =
                          Stmt.mk_assert_expr ~loc ~spec_error
                            (Expr.mk_eq ~loc inv.inv_snapshot
                               (Expr.mk_tuple ~loc full_args))
                        in
                        let stmt =
                          {
                            stmt with
                            stmt_desc = Basic (Use { use_desc with use_args = full_args });
                          }
                        in
                        Rewriter.return (Stmt.mk_block_stmt ~loc [ assert_stmt; stmt ])))
            | _ -> Error.internal_error stmt.stmt_loc "expected a predicate or invariant")
        | _ -> Error.internal_error stmt.stmt_loc "expected a call_def")
    | Basic (AUAction auaction_desc) -> (
        match auaction_desc.auaction_kind with
        | BindAU qual_iden ->
            let loc = Stmt.to_loc stmt in
            let* () =
              if
                List.exists atomicity_state.au_opened ~f:(fun au ->
                    Set.mem (Expr.local_vars au.token) (QualIdent.unqualify qual_iden))
              then
                Error.verification_error ~code:Error.Atomic_update loc
                  "An open atomic token cannot be rebound before commitAU or abortAU"
              else Rewriter.return ()
            in
            let* au_token_var_decl =
              let name =
                QualIdent.from_ident
                  (ProgUtils.callable_au_token_ident ~loc
                     (QualIdent.unqualify curr_callable_name))
              in
              let* symbol = Rewriter.find name in
              match Rewriter.Symbol.orig_symbol symbol with
              | VarDef _ -> Rewriter.Symbol.reify_var_decl symbol
              | _ -> Error.internal_error stmt.stmt_loc "expected a var_def"
            in

            let assign_stmt =
              Stmt.mk_assign ~loc [ qual_iden ] (Expr.from_var_decl au_token_var_decl)
            in
            let* () =
              Rewriter.set_user_state
                {
                  atomicity_state with
                  au_bindings =
                    Set.add atomicity_state.au_bindings (QualIdent.unqualify qual_iden);
                }
            in
            Rewriter.return assign_stmt
        | OpenAU open_au_desc ->
            let* callable, concrete_args, implicit_args =
              callable_info open_au_desc.proc_qi
            in
            let exhale_stmt =
              let error =
                ( Error.Verification Error.Atomic_token,
                  loc,
                  "Atomic token resource may not be available" )
              in
              Stmt.mk_exhale_expr
                ~cmnt:("OpenAU: " ^ Stmt.to_string stmt)
                ~spec_error:[ Stmt.mk_const_spec_error error ]
                ~loc
                (Expr.mk_app ~loc ~typ:Type.perm (AUPred open_au_desc.proc_qi)
                   [ open_au_desc.token; Expr.mk_tuple open_au_desc.proc_args ])
            in

            let* () =
              Rewriter.Logs.debug (fun printers m ->
                  m
                    "Elaboration.rewrite_au_cmnds: OpenAU: call_ident = %a; proc_args = \
                     %a; implicit_args = %a"
                    QualIdent.pr open_au_desc.proc_qi printers.pr_expr_list
                    open_au_desc.proc_args printers.pr_expr_list open_au_desc.lhs)
            in

            (* if *)
            let alpha_renaming_map =
              List.fold2_exn
                (concrete_args @ implicit_args)
                (open_au_desc.proc_args @ open_au_desc.lhs)
                ~init:(Map.empty (module QualIdent))
                ~f:(fun acc_map implicit_arg bound_var ->
                  Map.add_exn acc_map
                    ~key:(QualIdent.from_ident implicit_arg.var_name)
                    ~data:bound_var)
            in

            let inhale_stmts =
              List.filter_map callable.call_decl_precond ~f:(fun spec ->
                  if not spec.spec_atomic then None
                  else
                    Some
                      (Stmt.mk_inhale_expr
                         ~cmnt:("OpenAU: " ^ Stmt.to_string stmt)
                         ~loc
                         (Expr.alpha_renaming spec.spec_form alpha_renaming_map)))
            in

            let* flag, flag_init = fresh_updated_flag ~loc "$au_updated" in
            let* tracked_token =
              normalize_token
                { atomicity_state with au_bindings = prior_au_bindings }
                open_au_desc.token
            in
            let atomicity_state =
              open_au ~loc ~source_token:open_au_desc.token
                ( tracked_token,
                  open_au_desc.proc_qi,
                  open_au_desc.proc_args,
                  open_au_desc.lhs,
                  flag )
                atomicity_state
            in
            let* _ = Rewriter.set_user_state atomicity_state in

            let new_stmt =
              Stmt.mk_block_stmt ~loc ((exhale_stmt :: inhale_stmts) @ [ flag_init ])
            in

            Rewriter.return new_stmt
        | AbortAU _ | CommitAU _ ->
            let token =
              begin match auaction_desc.auaction_kind with
              | AbortAU au_desc -> au_desc.token
              | CommitAU au_desc -> au_desc.token
              | _ -> assert false
              end
            in
            let* tracked_token = normalize_token atomicity_state token in
            let opened_au_token =
              List.find atomicity_state.au_opened ~f:(fun au_token ->
                  Expr.alpha_equal au_token.token tracked_token)
            in

            let opened_au_token =
              match opened_au_token with
              | None ->
                  Error.verification_error ~code:Error.Atomic_update stmt.stmt_loc
                    (Printf.sprintf
                       !"Cannot %{String}: atomic token %{String} is not open"
                       (auaction_kind_to_string auaction_desc.auaction_kind)
                       (Expr.to_source_string token))
              | Some opened_au_token -> opened_au_token
            in

            let* callable_decl =
              let* symbol = Rewriter.find opened_au_token.callable in
              match Rewriter.Symbol.orig_symbol symbol with
              | CallDef _ -> Rewriter.Symbol.reify_callable_decl symbol
              | _ -> Error.internal_error stmt.stmt_loc "expected a call_def"
            in

            let* () =
              Rewriter.Logs.debug (fun printers m ->
                  m
                    "Elaboration.rewrite_au_cmnds: Abort/Commit AU: call_ident = %a; \
                     callable_args = %a"
                    QualIdent.pr opened_au_token.callable printers.pr_expr_list
                    (opened_au_token.callable_args @ opened_au_token.implicit_bound_vars))
            in

            let alpha_renaming_map = au_renaming callable_decl opened_au_token in

            let exhale_stmts, inhale_stmt, atomicity_state =
              match auaction_desc.auaction_kind with
              | AbortAU abort_au_desc ->
                  let loc = Stmt.to_loc stmt in

                  let exhale_stmts =
                    List.filter_map callable_decl.call_decl_precond ~f:(fun spec ->
                        if not spec.spec_atomic then None
                        else
                          let error =
                            ( Error.Verification Error.Abort,
                              loc,
                              "An atomic precondition may no longer hold when aborting \
                               the atomic update." )
                          in
                          Some
                            (Stmt.mk_exhale_expr
                               ~cmnt:("AbortAU: " ^ Stmt.to_string stmt)
                               ~loc
                               ~spec_error:
                                 (Stmt.mk_const_spec_error error :: spec.spec_error)
                               (Expr.alpha_renaming spec.spec_form alpha_renaming_map)))
                  in

                  let inhale_stmt =
                    Stmt.mk_inhale_expr
                      ~cmnt:("AbortAU: " ^ Stmt.to_string stmt)
                      ~loc
                      (Expr.mk_app ~loc ~typ:Type.perm (AUPred opened_au_token.callable)
                         [
                           opened_au_token.token;
                           Expr.mk_tuple opened_au_token.callable_args;
                         ])
                  in

                  let atomicity_state = close_au ~loc tracked_token atomicity_state in

                  (exhale_stmts, inhale_stmt, atomicity_state)
              | CommitAU commit_au_desc ->
                  let loc = Stmt.to_loc stmt in

                  let alpha_renaming_map =
                    List.fold2_exn callable_decl.call_decl_returns
                      commit_au_desc.proc_rets ~init:alpha_renaming_map
                      ~f:(fun acc_map formal_arg actual_arg ->
                        Map.add_exn acc_map
                          ~key:(QualIdent.from_ident formal_arg.var_name)
                          ~data:actual_arg)
                  in

                  let exhale_stmts =
                    List.filter_map callable_decl.call_decl_postcond ~f:(fun spec ->
                        if not spec.spec_atomic then None
                        else
                          let error =
                            ( Error.Verification Error.Commit,
                              loc,
                              "An atomic postcondition may not hold at this commit point"
                            )
                          in
                          Some
                            (Stmt.mk_exhale_expr
                               ~cmnt:("CommitAU: " ^ Stmt.to_string stmt)
                               ~loc
                               ~spec_error:
                                 (Stmt.mk_const_spec_error error :: spec.spec_error)
                               (Expr.alpha_renaming spec.spec_form alpha_renaming_map)))
                  in

                  let inhale_stmt =
                    Stmt.mk_inhale_expr
                      ~cmnt:("CommitAU: " ^ Stmt.to_string stmt)
                      ~loc
                      (Expr.mk_app ~loc ~typ:Type.perm
                         (AUPredCommit opened_au_token.callable)
                         [
                           opened_au_token.token;
                           Expr.mk_tuple opened_au_token.callable_args;
                           Expr.mk_tuple commit_au_desc.proc_rets;
                         ])
                  in

                  let atomicity_state = close_au ~loc tracked_token atomicity_state in

                  (exhale_stmts, inhale_stmt, atomicity_state)
              | _ -> assert false
            in

            let new_stmt = Stmt.mk_block_stmt ~loc (exhale_stmts @ [ inhale_stmt ]) in

            let* _ = Rewriter.set_user_state atomicity_state in

            Rewriter.return new_stmt)
    | StmtExt stmt_ext ->
        (* [Rewriter.Stmt.descend] deliberately doesn't enter a [StmtExt]'s
           nested statements (its hook is pinned to the unit user state), so
           whatever they are is folded into the extension's own answer here. *)
        let* ext_hooks = Rewriter.current_ext_hooks in
        let atomicity_state =
          drop_stale_idents
            ~idents:(ext_hooks.stmt_ext_local_vars_modified stmt_ext)
            atomicity_state
        in
        let atomicity_state =
          take_ext_step ~loc (ext_hooks.stmt_ext_atomicity stmt_ext) atomicity_state
        in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Block { block_kind = Atomic; _ } ->
        (* `--strict`: the block is the one construct whose claim the verifier takes on
           trust rather than checking -- there is no model of the target machine, and no
           scheduler, to check it against. That puts it in the same class as an explicit
           `free`, which `--strict` already flags, so flag it here too.

           No library-source exclusion needed here, unlike the `free`/`decreases`
           warnings: the standard library is loaded with [Ast.Module.set_unit_free],
           which strips a concrete proc's body before type-checking even begins, so an
           embedded primitive's `atomic` block never reaches this rewrite pass at all --
           there is nothing here to warn about. (A file checked directly as an ordinary
           program, library source or not, is never force-freed and is genuinely
           reverified, so it warns like any other input -- as it should.) *)
        let* () =
          let* cli_config = Rewriter.current_cli_config in
          if not cli_config.cli_strict then Rewriter.return ()
          else
            Rewriter.warning loc
              "this `atomic` block's body is assumed to be a single machine step, not \
               checked; Raven has no model of the target machine to verify that against"
        in
        (* One step to the enclosing context, however many statements inside. *)
        let outer = take_atomic_step ~loc atomicity_state in
        let* _ = Rewriter.set_user_state { outer with in_atomic_block = true } in
        let* stmt = Rewriter.Stmt.descend stmt ~f:rewrite_au_cmnds in
        let* inner = Rewriter.current_user_state in
        (* Anything opened inside must be closed inside: an invariant held across
           the block's boundary is held across a step boundary, which is what the
           one-step rule exists to police. The same instances must be open on
           both sides, not merely as many. *)
        let* () =
          (* At most one AU is open at a time (see [open_au]), so plain list
             equality is order-insensitive there. *)
          if
            same_open_invs inner.invs_opened outer.invs_opened
            && List.equal same_open_au inner.au_opened outer.au_opened
          then Rewriter.return ()
          else
            Error.verification_error ~code:Error.Atomicity loc
              "An invariant or atomic update opened inside an atomic block must also be \
               closed inside it"
        in
        (* A close inside the body clears the step flag, but the block's step
           still counts against whatever is open after it. *)
        let* _ =
          Rewriter.set_user_state
            {
              inner with
              in_atomic_block = outer.in_atomic_block;
              atomic_step_taken = outer.atomic_step_taken;
            }
        in
        Rewriter.return stmt
    | Cond cond_desc ->
        let* then_stmt = rewrite_au_cmnds cond_desc.cond_then in
        let* then_atomicity_state = Rewriter.current_user_state in

        let* _ = Rewriter.set_user_state atomicity_state in
        let* else_stmt = rewrite_au_cmnds cond_desc.cond_else in
        let* else_atomicity_state = Rewriter.current_user_state in

        let if_else_atomicity_states_equal =
          same_open_invs then_atomicity_state.invs_opened else_atomicity_state.invs_opened
          && List.equal same_open_au then_atomicity_state.au_opened
               else_atomicity_state.au_opened
        in

        if if_else_atomicity_states_equal then
          (* Obligations from either arm survive; credit must hold on both arms. *)
          let else_atomicity_state =
            {
              else_atomicity_state with
              mask =
                Callable.mask_inter then_atomicity_state.mask else_atomicity_state.mask;
              separation =
                union_separation then_atomicity_state.separation
                  else_atomicity_state.separation;
              callees =
                Set.union then_atomicity_state.callees else_atomicity_state.callees;
              au_bindings =
                Set.inter then_atomicity_state.au_bindings
                  else_atomicity_state.au_bindings;
              invs_opened =
                join_ghost_updates ~from:then_atomicity_state.invs_opened
                  else_atomicity_state.invs_opened;
              au_opened =
                join_au_updates ~from:then_atomicity_state.au_opened
                  else_atomicity_state.au_opened;
              preds_unfolded =
                common_preds_unfolded then_atomicity_state.preds_unfolded
                  else_atomicity_state.preds_unfolded;
            }
          in
          let* _ = Rewriter.set_user_state else_atomicity_state in
          let then_stmt =
            match
              snapshot_sync_stmts ~loc ~from:then_atomicity_state.invs_opened
                ~into:else_atomicity_state.invs_opened
              @ au_flag_sync_stmts ~loc ~from:then_atomicity_state.au_opened
                  ~into:else_atomicity_state.au_opened
            with
            | [] -> then_stmt
            | sync -> Stmt.mk_block_stmt ~loc (then_stmt :: sync)
          in
          let new_stmt =
            {
              stmt with
              stmt_desc =
                Cond { cond_desc with cond_then = then_stmt; cond_else = else_stmt };
            }
          in

          if is_ghost_scope then Rewriter.return new_stmt
          else
            (* The conditional itself is not a step: evaluating the test is
               thread-local (heap reads aren't permitted in a condition, so
               it only inspects locals) and hence unobservable by interfering
               threads. Only one arm runs, so the pair costs whatever the
               more expensive arm costs -- taking the disjunction here lets a
               conditional whose arms each take a single atomic step sit
               inside an open invariant or atomic update, while still
               rejecting a further step after the join. *)
            let atomicity_state =
              {
                else_atomicity_state with
                atomic_step_taken =
                  then_atomicity_state.atomic_step_taken
                  || else_atomicity_state.atomic_step_taken;
              }
            in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return new_stmt
        else
          Error.verification_error ~code:Error.Atomicity stmt.stmt_loc
            "Inconsistent atomicity states in then and else branches"
    | Loop _ when Option.is_some atomicity_state.namespace_draft ->
        Error.internal_error loc
          "Namespace atomicity analysis requires loops to be desugared first"
    | Loop _ ->
        let written = Set.of_list (module Ident) (Stmt.stmt_local_vars_modified stmt) in
        let bindings = Set.diff atomicity_state.au_bindings written in
        let* () =
          Rewriter.set_user_state { atomicity_state with au_bindings = bindings }
        in
        let* stmt = Rewriter.Stmt.descend stmt ~f:rewrite_au_cmnds in
        let* state = Rewriter.current_user_state in
        let* () =
          Rewriter.set_user_state
            { state with au_bindings = Set.inter bindings state.au_bindings }
        in
        Rewriter.return stmt
    | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_au_cmnds
  in

  let* stmt = rewrite_au_cmnds stmt in
  let* atomicity_state = Rewriter.current_user_state in

  if List.is_empty atomicity_state.au_opened && List.is_empty atomicity_state.invs_opened
  then Rewriter.return stmt
  else unclosed_error ~body_loc:stmt.stmt_loc atomicity_state

let analyze ?namespace_draft (c : Callable.t) : (namespace_analysis, 'a) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let* scope_id = Rewriter.current_scope_id in
  let* mask, separation =
    match namespace_draft with
    | None ->
        let+ mask =
          Masks.resolve_mask (Option.value c.call_decl.call_decl_needs_mask ~default:[])
        in
        (mask, [])
    | Some draft ->
        let+ summary = NamespaceInference.find_callable draft scope_id in
        let summary = Option.value_exn summary in
        (summary.requires, summary.separation)
  in
  Logs.debug (fun m ->
      m
        "Elaboration.rewrite_atomicity_analysis: Rewriting atomicity analysis for \
         callable: %a"
        QualIdent.pr scope_id);
  Rewriter.eval_with_user_state
    ~init:
      {
        au_opened = [];
        au_bindings = Set.empty (module Ident);
        invs_opened = [];
        preds_unfolded = [];
        atomic_step_taken = false;
        in_atomic_block = false;
        mask;
        namespace_draft;
        separation;
        callees = Set.empty (module QualIdent);
      }
    (let* callable = Rewriter.Callable.rewrite_stmts ~f:rewrite_au_cmnds c in
     let+ (state : atomicity_check) = Rewriter.current_user_state in
     { callable; separation = state.separation; callees = state.callees })

let rewrite_atomicity_analysis c =
  let open Rewriter.Syntax in
  let+ analysis = analyze c in
  analysis.callable

(** Collect draft assumptions after elaboration preparation (including loop desugaring),
    without installing a frozen contract. *)
let collect_namespace_requirements draft c = analyze ~namespace_draft:draft c
