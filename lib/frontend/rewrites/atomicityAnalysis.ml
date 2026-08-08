open Base
open Ast
open Ast.Stmt
open Ast.Expr
open Util

type au_token = {
  token : Expr.t;
  callable : QualIdent.t;
  callable_args : expr list;
  implicit_bound_vars : expr list;
  (* Where the [openAU] was, so a never-committed update can point back at it. *)
  au_loc : location;
}

type invs = {
  inv_name : QualIdent.t;
  inv_args : Expr.t list;
  (* Where the [unfold] was, so a never-folded instance can point back at it. *)
  inv_loc : location;
  (* Snapshot of [inv_args]' values at the moment this instance was opened,
     in a fresh ghost local. The matching [fold] must prove its own
     arguments equal this snapshot, since a local variable in [inv_args] can
     be reassigned between [unfold] and [fold] with no argument-value check
     otherwise catching it (reassignment isn't an atomic step). *)
  inv_snapshot : Expr.t;
  (* The mask entry consumed from [atomicity_check.mask] to open this
     instance (see [open_inv]); restored verbatim on the matching close (see
     [close_inv]). *)
  inv_consumed_mask_entry : Callable.mask_entry;
}

type atomicity_check = {
  au_opened : au_token list;
  invs_opened : invs list;
  atomic_step_taken : bool;
  mask : Callable.mask;
  (* Set while analysing the body of a physically atomic block. The block as a
     whole already cost one step in the enclosing context, and no intermediate
     state inside it is observable, so step counting is suspended within.
     Invariant and atomic-update tracking continues, so anything opened inside
     must still be closed inside. *)
  in_atomic_block : bool;
}

(* Renders an open instance the way the [unfold] named it, e.g. [i(x)]. *)
let inv_to_string (inv : invs) : string =
  let name = Ident.to_string (QualIdent.unqualify inv.inv_name) in
  match inv.inv_args with
  | [] -> name
  | args ->
      name ^ "("
      ^ String.concat ~sep:", " (List.map args ~f:Expr.to_source_string)
      ^ ")"

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
    let token = Expr.to_source_string au.token in
    ( Printf.sprintf
        "Missing commitAU or abortAU for open atomic update %s" token,
      au.au_loc,
      Printf.sprintf "%s was opened here" token )
  in
  let entries =
    List.map state.invs_opened ~f:inv_entry
    @ List.map state.au_opened ~f:au_entry
  in
  match entries with
  | [] ->
      Error.internal_error body_loc
        "unclosed_error called with nothing left open"
  | (msg, rel_loc, rel_msg) :: rest ->
      Error.fail_with
        ((Error.Verification, Loc.last_char body_loc, msg)
        :: (Error.RelatedLoc, rel_loc, rel_msg)
        :: List.map rest ~f:(fun (msg, rel_loc, _) ->
               (Error.RelatedLoc, rel_loc, msg)))

let list_remove_first (lst : 'a list) ~(f : 'a -> bool) : 'a list =
  let rec go = function
    | [] -> []
    | x :: xs -> if f x then xs else x :: go xs
  in
  go lst

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

(* [args1]/[args2] are both full argument lists for the same invariant
   declaration (hence the same length -- same formal arity). [Error ()]
   means every position is syntactically identical: definitely the same
   instance, not disjoint, no point asking Z3. [Ok cond] is the disjunction
   of pairwise disequalities at positions that aren't already syntactically
   identical -- discharging it proves the two instances are disjoint. This
   is the disjointness half of the matching procedure. *)
let disjointness_condition ~loc (args1 : Expr.t list) (args2 : Expr.t list) :
    (Expr.t, unit) Result.t =
  let diffs =
    List.filter_map (List.zip_exn args1 args2) ~f:(fun (a, b) ->
        if Expr.alpha_equal a b then None
        else Some (Expr.mk_not ~loc (Expr.mk_eq ~loc a b)))
  in
  match diffs with [] -> Error () | _ -> Ok (Expr.mk_or ~loc diffs)

(* Finds which (if any) already-open instance of [inv_name] a [fold]
   supplying [use_args] closes: an exact syntactic ([alpha_equal]) match if
   one exists (unambiguous), else -- since multiple instances of the same
   declaration can be open at once -- the first candidate found, relying on
   the drift-detecting snapshot-equality assert below to reject a wrong
   guess. [None] means this is a fresh allocation, not a close. *)
let find_matching_open_inv (atomicity_state : atomicity_check)
    (inv_name : QualIdent.t) (use_args : Expr.t list) : invs option =
  let candidates =
    List.filter atomicity_state.invs_opened ~f:(fun inv ->
        QualIdent.equal inv.inv_name inv_name)
  in
  match
    List.find candidates ~f:(fun inv ->
        List.for_all2_exn inv.inv_args use_args ~f:Expr.alpha_equal)
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
        Error.verification_error loc
          "Attempting to take more than one atomic step with an open invariant \
           or atomic update"

let take_non_atomic_step ~loc (state : atomicity_check) : atomicity_check =
  if state.in_atomic_block then state
  else if List.is_empty state.au_opened && List.is_empty state.invs_opened then state
  else
    Error.verification_error loc
      "Cannot take a non-atomic step while an invariant or atomic update is open"

(* An extension statement is opaque here -- this pass has to run before the
   lowering that would reveal what it does, since e.g. a `cas` lowers to a read
   plus a conditional write yet is a single machine instruction. So the active
   extension declares the cost; see [Stmt.stmt_atomicity]. *)
let take_ext_step ~loc (atomicity : Stmt.stmt_atomicity) (state : atomicity_check)
    : atomicity_check =
  match atomicity with
  | NoStep -> state
  | AtomicStep -> take_atomic_step ~loc state
  | NonAtomicStep -> take_non_atomic_step ~loc state

(* Returns the extra assert statements (reentrancy guard + membership proof)
   the caller must splice in immediately before the [Unfold] statement,
   together with the updated state. *)
let open_inv ~loc (inv_name, inv_args, inv_snapshot) atomicity_state :
    atomicity_check * Stmt.t list =
  (* Reentrancy guard: this instance must be disjoint from every instance of
     the same declaration already open -- not decidable by name alone, since
     multiple instances of one declaration can be open simultaneously. *)
  let same_name_open =
    List.filter atomicity_state.invs_opened ~f:(fun inv ->
        QualIdent.equal inv.inv_name inv_name)
  in
  let reentrancy_asserts =
    List.map same_name_open ~f:(fun inv ->
        match disjointness_condition ~loc inv_args inv.inv_args with
        | Error () ->
            Error.verification_error loc
              (Printf.sprintf !"Invariant %{Ident} is already open"
                 (inv_name |> QualIdent.unqualify))
        | Ok cond ->
            let spec_error =
              let error =
                ( Error.Verification,
                  loc,
                  Printf.sprintf
                    !"Cannot unfold %{Ident}: this instance may be the same \
                      as one already open (arguments identifying the two \
                      instances are not provably distinct)"
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
    List.filter atomicity_state.mask ~f:(fun (qi, _) ->
        QualIdent.equal qi inv_name)
  in
  let scored =
    List.filter_map candidates ~f:(fun (qi, args) ->
        match membership_conditions ~loc ~candidate:args ~target:inv_args with
        | None -> None
        | Some conds -> Some ((qi, args), conds))
  in
  let chosen, membership_conds =
    match List.find scored ~f:(fun (_, conds) -> List.is_empty conds) with
    | Some (entry, conds) -> (entry, conds)
    | None -> (
        match scored with
        | [] ->
            Error.verification_error loc
              (Printf.sprintf
                 !"Invariant %{Ident} is not in the current mask"
                 (inv_name |> QualIdent.unqualify))
        | (entry, conds) :: _ -> (entry, conds))
  in
  let membership_asserts =
    List.map membership_conds ~f:(fun cond ->
        let spec_error =
          let error =
            ( Error.Verification,
              loc,
              Printf.sprintf
                !"Cannot unfold %{Ident}: the available mask entry's \
                  arguments are not provably equal to this instance's"
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
  List.concat_map required ~f:(fun (qi, args) ->
      let same_name_open =
        List.filter atomicity_state.invs_opened ~f:(fun inv ->
            QualIdent.equal inv.inv_name qi)
      in
      List.map same_name_open ~f:(fun inv ->
          match disjointness_condition ~loc args inv.inv_args with
          | Error () ->
              Error.verification_error loc
                (Printf.sprintf !"Invariant %{Ident} is already open"
                   (qi |> QualIdent.unqualify))
          | Ok cond ->
              let spec_error =
                let error =
                  ( Error.Verification,
                    loc,
                    Printf.sprintf
                      !"Cannot call this here: the invariant %{Ident} \
                        required by the callee may be the same instance as \
                        one already open (arguments identifying the two \
                        instances are not provably distinct)"
                      (qi |> QualIdent.unqualify) )
                in
                [ Stmt.mk_const_spec_error error ]
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
        mask = Callable.mask_union atomicity_state.mask [ (inv_name, inv_args) ];
      }
  | Some inv ->
      let invs_opened =
        list_remove_first atomicity_state.invs_opened ~f:(fun i ->
            QualIdent.equal i.inv_name inv.inv_name
            && List.for_all2_exn i.inv_args inv.inv_args ~f:Expr.alpha_equal)
      in
      let mask =
        Callable.mask_union atomicity_state.mask [ inv.inv_consumed_mask_entry ]
      in
      if List.is_empty invs_opened && List.is_empty atomicity_state.au_opened then
        { atomicity_state with invs_opened; mask; atomic_step_taken = false }
      else { atomicity_state with invs_opened; mask }

let open_au ~loc (token, callable, callable_args, implicit_bound_vars)
    atomicity_state : atomicity_check =
  if
    List.exists atomicity_state.au_opened ~f:(fun au ->
        Expr.alpha_equal au.token token)
  then
    Error.verification_error loc
      (Printf.sprintf !"Atomic token %{String} is already open"
         (Expr.to_source_string token))
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
    Error.verification_error loc
      (Printf.sprintf
         !"Cannot open atomic token %{String} while another atomic update \
           is still open; commit or abort it first"
         (Expr.to_source_string token))
  else
    {
      atomicity_state with
      au_opened =
        { token; callable; callable_args; implicit_bound_vars; au_loc = loc }
        :: atomicity_state.au_opened;
    }

let close_au ~loc token atomicity_state : atomicity_check =
  if
    not
      (List.exists atomicity_state.au_opened ~f:(fun au ->
           Expr.alpha_equal au.token token))
  then
    Error.verification_error loc
      (Printf.sprintf !"Atomic token %{String} is not open (nothing to close)"
         (Expr.to_source_string token))
  else
    let au_opened =
      List.filter atomicity_state.au_opened ~f:(fun au ->
          not (Expr.alpha_equal au.token token))
    in

    if List.is_empty au_opened && List.is_empty atomicity_state.invs_opened then
      { atomicity_state with au_opened; atomic_step_taken = false }
    else { atomicity_state with au_opened }


let rewrite_au_cmnds (stmt : Stmt.t) : (Stmt.t, atomicity_check) Rewriter.t_ext
    =
  let open Rewriter.Syntax in
  let rec rewrite_au_cmnds (stmt : Stmt.t) :
      (Stmt.t, atomicity_check) Rewriter.t_ext =
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    let* curr_callable_name = Rewriter.current_scope_id in

    let callable_info call_ident =
      let+ callable = Rewriter.find_and_reify_callable call_ident in
     
      let concrete_args =
        List.filter callable.call_decl.call_decl_formals ~f:(fun var_decl ->
            not var_decl.var_implicit)
      in
      let implicit_args =
        List.filter callable.call_decl.call_decl_formals ~f:(fun var_decl ->
            var_decl.var_implicit)
      in
      callable, concrete_args, implicit_args
    in

    let* () = Rewriter.Logs.debug (fun printers m ->
        m "Rewrites.rewrite_au_cmnds: curr_callable_name: %a; stmt=%a" QualIdent.pr
          curr_callable_name printers.pr_stmt stmt) in

    let loc = stmt.stmt_loc in

    let* atomicity_state = Rewriter.current_user_state in

    (* Assigned-variable-drops mask entries mentioning them; see
       [drop_mask_entries_mentioning]'s doc comment. The arguments are the
       (possibly ghost) variables this statement writes to. *)
    let drop_stale_idents ~(idents : Ident.t list) (state : atomicity_check) :
        atomicity_check =
      let assigned = Set.of_list (module Ident) idents in
      { state with mask = drop_mask_entries_mentioning assigned state.mask }
    in
    let drop_stale ~(qis : QualIdent.t list) (state : atomicity_check) :
        atomicity_check =
      drop_stale_idents ~idents:(List.map qis ~f:QualIdent.unqualify) state
    in

    match stmt.stmt_desc with
    | Basic (New new_desc) ->
        let* new_lhs =
          let* symbol = Rewriter.find_and_reify new_desc.new_lhs in
          match symbol with
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
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (Bind bind_desc) ->
        let atomicity_state = drop_stale ~qis:bind_desc.bind_lhs atomicity_state in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (FieldRead field_read_desc) -> (
        let* symbol = Rewriter.find_and_reify field_read_desc.field_read_lhs in
        let atomicity_state =
          drop_stale ~qis:[ field_read_desc.field_read_lhs ] atomicity_state
        in
        match symbol with
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
        let* symbol =
          Rewriter.find_and_reify field_write_desc.field_write_field
        in
        match symbol with
        | FieldDef fld ->
            if fld.field_is_ghost then Rewriter.return stmt
            else
              let atomicity_state = take_atomic_step ~loc atomicity_state in
              let* _ = Rewriter.set_user_state atomicity_state in
              Rewriter.return stmt
        | _ -> Error.internal_error stmt.stmt_loc "expected a field_def")
    | Basic (Havoc hvc) ->
        let atomicity_state = drop_stale ~qis:[ hvc.havoc_var ] atomicity_state in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (Call call_desc) ->
        let* symbol = Rewriter.find_and_reify call_desc.call_name in
        let call_decl, call_def =
          match symbol with
          | CallDef c -> (c.call_decl, c.call_def)
          | _ -> Error.internal_error stmt.stmt_loc "expected a call_def"
        in

        (* The callee's mask entries are expressed in terms of its own
           formals; substitute the actual call arguments before comparing
           against the caller's (locals-relative) mask. Kept purely
           syntactic here (no SMT-backed matching, unlike [open_inv]): an
           ordinary call never needs to splice in extra statements the way
           [Unfold] does, and any mask entry [membership_conditions] would
           need an assert for at a call site could instead just be written
           more precisely by the caller.

           Substitution is only attempted when the callee's mask actually
           has a non-empty (fine-grained) entry -- the overwhelming common
           case is every entry being the coarse [], which needs no
           substitution at all, and formal/actual alignment (concrete vs.
           `implicit`, which callers may or may not supply explicitly) isn't
           always simply "drop the implicit formals" -- see e.g.
           `acquire(l, r, b1)` explicitly supplying implicit formals in
           test/concurrent/lock/spin-lock.rav. A length mismatch falls back
           to no substitution rather than aborting, so a genuine alignment
           gap surfaces as an ordinary (safe) mask-unavailability error
           instead of crashing the compiler. *)
        let callee_mask = Option.value_exn call_decl.call_decl_needs_mask in
        let needs_substitution =
          List.exists callee_mask ~f:(fun (_, args) -> not (List.is_empty args))
        in
        let required_at_call_site =
          if not needs_substitution then callee_mask
          else
            let renaming_map =
              match
                List.fold2 call_decl.call_decl_formals call_desc.call_args
                  ~init:(Map.empty (module QualIdent))
                  ~f:(fun acc formal actual ->
                    Map.set acc
                      ~key:(QualIdent.from_ident formal.var_name)
                      ~data:actual)
              with
              | Ok m -> m
              | Unequal_lengths -> Map.empty (module QualIdent)
            in
            List.map callee_mask ~f:(fun (qi, args) ->
                (qi, List.map args ~f:(fun e -> Expr.alpha_renaming e renaming_map)))
        in
        let missing =
          List.find required_at_call_site ~f:(fun (qi, args) ->
              let candidates =
                List.filter atomicity_state.mask ~f:(fun (qi', _) ->
                    QualIdent.equal qi' qi)
              in
              not
                (List.exists candidates ~f:(fun (_, cand_args) ->
                     match
                       membership_conditions ~loc ~candidate:cand_args
                         ~target:args
                     with
                     | Some [] -> true
                     | None | Some (_ :: _) -> false)))
        in

        if Option.is_some missing then
          let msg =
            let missing_inv, _ = Option.value_exn missing in
            let call_id = call_desc.call_name |> QualIdent.unqualify in
            Printf.sprintf
              !"Cannot call %{Ident}. The invariant %{Ident} required by \
                %{Ident} is not available in the current mask"
              call_id (missing_inv |> QualIdent.unqualify) call_id
          in
          Error.verification_error stmt.stmt_loc msg
        else
          let reentrancy_asserts =
            call_reentrancy_asserts ~loc atomicity_state required_at_call_site
          in
          let* is_call_lhs_ghost =
            Rewriter.List.for_all call_desc.call_lhs ~f:(fun qual_iden ->
                let* symbol = Rewriter.find_and_reify qual_iden in
                match symbol with
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
             including the ghost-lhs/[Lemma]
             one, which otherwise never touches [atomicity_state] at all,
             since a lemma can still fold a fresh invariant and hand its
             credit onward exactly like a proc can. Substituted through both
             the actual call arguments (the callee's own formals) and the
             call's lhs bindings (the callee's own return variables), since
             a grants-set entry -- unlike [call_decl_needs_mask] -- can be
             expressed via either. *)
          let* atomicity_state =
            match Option.value call_decl.call_decl_grants_mask ~default:[] with
            | [] -> Rewriter.return atomicity_state
            | grants ->
                let needs_substitution =
                  List.exists grants ~f:(fun (_, args) -> not (List.is_empty args))
                in
                if not needs_substitution then
                  Rewriter.return
                    { atomicity_state with mask = Callable.mask_union atomicity_state.mask grants }
                else
                  let formal_map =
                    match
                      List.fold2 call_decl.call_decl_formals call_desc.call_args
                        ~init:(Map.empty (module QualIdent))
                        ~f:(fun acc formal actual ->
                          Map.set acc
                            ~key:(QualIdent.from_ident formal.var_name)
                            ~data:actual)
                    with
                    | Ok m -> m
                    | Unequal_lengths -> Map.empty (module QualIdent)
                  in
                  let renaming_map =
                    match
                      List.fold2 call_decl.call_decl_returns call_desc.call_lhs
                        ~init:formal_map
                        ~f:(fun acc ret lhs ->
                          Map.set acc
                            ~key:(QualIdent.from_ident ret.var_name)
                            ~data:(Expr.mk_var ~typ:ret.var_type lhs))
                    with
                    | Ok m -> m
                    | Unequal_lengths -> formal_map
                  in
                  let credited =
                    List.map grants ~f:(fun (qi, args) ->
                        ( qi,
                          List.map args ~f:(fun e -> Expr.alpha_renaming e renaming_map) ))
                  in
                  Rewriter.return
                    { atomicity_state with mask = Callable.mask_union atomicity_state.mask credited }
          in

          if
            (is_call_lhs_ghost && not (List.is_empty call_desc.call_lhs))
            || Poly.(call_decl.call_decl_kind = Lemma)
          then
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return
              (Stmt.mk_block_stmt ~loc (reentrancy_asserts @ [ stmt ]))
          else if Callable.is_atomic call_decl then
            let atomicity_state = take_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return
              (Stmt.mk_block_stmt ~loc (reentrancy_asserts @ [ stmt ]))
          else
            let atomicity_state = take_non_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return
              (Stmt.mk_block_stmt ~loc (reentrancy_asserts @ [ stmt ]))
    | Basic (BasicStmtExt (stmt_ext, args)) ->
        let* ext_hooks = Rewriter.current_ext_hooks in
        let atomicity_state =
          drop_stale_idents
            ~idents:(ext_hooks.basic_stmt_ext_local_vars_modified stmt_ext args)
            atomicity_state
        in
        let atomicity_state =
          take_ext_step ~loc (ext_hooks.stmt_ext_atomicity stmt_ext)
            atomicity_state
        in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (Return return_expr) ->
        let atomicity_state = take_atomic_step ~loc atomicity_state in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (Use use_desc) -> (
        let* symbol = Rewriter.find_and_reify use_desc.use_name in
        match symbol with
        | CallDef c -> (
            match c.call_decl.call_decl_kind with
            | Pred -> Rewriter.return stmt
            | Invariant -> (
                match use_desc.use_kind with
                | Unfold ->
                    (* See [invs.inv_snapshot]. Skip for 0-arity invariants
                       (e.g. [inv inv1() { ... }]): only one instance is
                       possible, so there's no identity to freeze. *)
                    let* snap_expr, snap_stmts =
                      match use_desc.use_args with
                      | [] -> Rewriter.return (Expr.mk_bool ~loc true, [])
                      | _ :: _ ->
                          let snap_ident =
                            Ident.fresh loc
                              ("$inv_snapshot_"
                              ^ Ident.to_string
                                  (QualIdent.unqualify use_desc.use_name))
                          in
                          let snap_type =
                            Type.mk_prod loc
                              (List.map use_desc.use_args ~f:Expr.to_type)
                          in
                          let snap_var_decl =
                            Type.mk_var_decl ~ghost:true ~loc snap_ident
                              snap_type
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
                            Expr.mk_var ~typ:snap_type
                              (QualIdent.from_ident snap_ident)
                          in
                          let snap_assign_stmt =
                            Stmt.mk_assign ~loc ~is_init:true
                              [ QualIdent.from_ident snap_ident ]
                              (Expr.mk_tuple ~loc use_desc.use_args)
                          in
                          (snap_expr, [ snap_assign_stmt ])
                    in
                    let atomicity_state, open_asserts =
                      open_inv ~loc
                        (use_desc.use_name, use_desc.use_args, snap_expr)
                        atomicity_state
                    in
                    let* _ = Rewriter.set_user_state atomicity_state in
                    Rewriter.return
                      (Stmt.mk_block_stmt ~loc
                         (open_asserts @ snap_stmts @ [ stmt ]))
                | Fold ->
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
                      close_inv ~inv_name:use_desc.use_name
                        ~inv_args:use_desc.use_args matching_open_inv
                        atomicity_state
                    in
                    let* _ = Rewriter.set_user_state atomicity_state in
                    (match matching_open_inv, use_desc.use_args with
                    | None, _ | _, [] ->
                        (* Fresh allocation, or 0-arity (no snapshot exists). *)
                        Rewriter.return stmt
                    | Some inv, _ :: _ ->
                        let spec_error =
                          let error =
                            ( Error.Verification,
                              loc,
                              Printf.sprintf
                                !"Cannot fold %{Ident}: its arguments no \
                                  longer match the instance that was opened \
                                  by the corresponding unfold (a variable \
                                  used to identify the instance may have \
                                  been reassigned in between)"
                                (use_desc.use_name |> QualIdent.unqualify) )
                          in
                          [ Stmt.mk_const_spec_error error ]
                        in
                        let assert_stmt =
                          Stmt.mk_assert_expr ~loc ~spec_error
                            (Expr.mk_eq ~loc inv.inv_snapshot
                               (Expr.mk_tuple ~loc use_desc.use_args))
                        in
                        Rewriter.return
                          (Stmt.mk_block_stmt ~loc [ assert_stmt; stmt ])))
            | _ -> Error.internal_error stmt.stmt_loc "expected a predicate or invariant")
        | _ -> Error.internal_error stmt.stmt_loc "expected a call_def")
    | Basic (AUAction auaction_desc) -> (
        match auaction_desc.auaction_kind with
        | BindAU qual_iden ->
            let loc = Stmt.to_loc stmt in
            let* qual_iden_var =
              let+ symbol = Rewriter.find_and_reify qual_iden in
              match symbol with
              | VarDef v -> v
              | _ -> Error.internal_error stmt.stmt_loc "expected a var_def"
            in

            let* au_token_var =
              let+ symbol =
                Rewriter.find_and_reify
                  (QualIdent.from_ident
                     (ProgUtils.callable_au_token_ident ~loc
                        (QualIdent.unqualify curr_callable_name)))
              in
              match symbol with
              | VarDef v -> v
              | _ -> Error.internal_error stmt.stmt_loc "expected a var_def"
            in

            let assign_stmt =
              Stmt.mk_assign ~loc [ qual_iden ]
                (Expr.from_var_decl au_token_var.var_decl)
            in

            Rewriter.return assign_stmt
        | OpenAU open_au_desc -> (
            let* callable, concrete_args, implicit_args = callable_info open_au_desc.proc_qi in
            let exhale_stmt =
              let error =
              ( Error.Verification,
                loc,
                "Atomic token resource may not be available" )
              in
              Stmt.mk_exhale_expr
                ~cmnt:("OpenAU: " ^ Stmt.to_string stmt)
                ~spec_error:[Stmt.mk_const_spec_error error]
                ~loc
                (Expr.mk_app ~loc ~typ:Type.perm (AUPred open_au_desc.proc_qi)
                   [open_au_desc.token; (Expr.mk_tuple open_au_desc.proc_args)])
            in

            let* () = Rewriter.Logs.debug (fun printers m -> m "Rewrites.rewrite_au_cmnds: OpenAU: call_ident = %a; proc_args = %a; implicit_args = %a" QualIdent.pr open_au_desc.proc_qi printers.pr_expr_list open_au_desc.proc_args printers.pr_expr_list open_au_desc.lhs) in

            (* if *)

            let alpha_renaming_map =
              List.fold2_exn (concrete_args @ implicit_args) (open_au_desc.proc_args @ open_au_desc.lhs)
                ~init:(Map.empty (module QualIdent))
                ~f:(fun acc_map implicit_arg bound_var ->
                    Map.add_exn acc_map
                      ~key:(QualIdent.from_ident implicit_arg.var_name)
                      ~data:bound_var)
            in

            let inhale_stmts =
              List.filter_map callable.call_decl.call_decl_precond
                ~f:(fun spec ->
                    if not spec.spec_atomic then None
                    else
                      Some
                        (Stmt.mk_inhale_expr
                           ~cmnt:("OpenAU: " ^ Stmt.to_string stmt)
                           ~loc
                           (Expr.alpha_renaming spec.spec_form
                              alpha_renaming_map)))
            in

            let atomicity_state =
              open_au ~loc
                ( open_au_desc.token,
                  open_au_desc.proc_qi,
                  open_au_desc.proc_args,
                  open_au_desc.lhs )
                atomicity_state
            in
            let* _ = Rewriter.set_user_state atomicity_state in
            
            let new_stmt =
              Stmt.mk_block_stmt ~loc (exhale_stmt :: inhale_stmts)
            in

            Rewriter.return new_stmt)
        | AbortAU _ | CommitAU _ ->
            let token = begin match auaction_desc.auaction_kind with
              | AbortAU au_desc -> au_desc.token
              | CommitAU au_desc -> au_desc.token
              | _ -> assert false
              end 
            in
            let opened_au_token =
              List.find atomicity_state.au_opened ~f:(fun au_token ->
                  Expr.alpha_equal au_token.token token)
            in

            let opened_au_token =
              match opened_au_token with
              | None ->
                  Error.verification_error stmt.stmt_loc
                    (Printf.sprintf
                       !"Cannot %{String}: atomic token %{String} is not open"
                       (auaction_kind_to_string auaction_desc.auaction_kind)
                       (Expr.to_source_string token))
              | Some opened_au_token -> opened_au_token
            in

            let* callable_decl =
              let+ symbol = Rewriter.find_and_reify opened_au_token.callable in
              match symbol with
              | CallDef c -> c.call_decl
              | _ -> Error.internal_error stmt.stmt_loc "expected a call_def"
            in

            let* () = Rewriter.Logs.debug (fun printers m -> m "Rewrites.rewrite_au_cmnds: Abort/Commit AU: call_ident = %a; callable_args = %a" QualIdent.pr opened_au_token.callable printers.pr_expr_list (opened_au_token.callable_args
               @ opened_au_token.implicit_bound_vars)) in


            let alpha_renaming_map =
              List.fold2_exn callable_decl.call_decl_formals
                (opened_au_token.callable_args
               @ opened_au_token.implicit_bound_vars)
                ~init:(Map.empty (module QualIdent))
                ~f:(fun acc_map formal_arg actual_arg ->
                  Map.add_exn acc_map
                    ~key:(QualIdent.from_ident formal_arg.var_name)
                    ~data:actual_arg)
            in

            let exhale_stmts, inhale_stmt, atomicity_state =
              match auaction_desc.auaction_kind with
              | AbortAU abort_au_desc ->
                  let loc = Stmt.to_loc stmt in

                  let exhale_stmts =
                    List.filter_map callable_decl.call_decl_precond
                      ~f:(fun spec ->
                        if not spec.spec_atomic then None
                        else
                          let error =
                            ( Error.Verification,
                              loc,
                              "An atomic precondition may no longer hold when \
                               aborting the atomic update." )
                          in
                          Some
                            (Stmt.mk_exhale_expr
                               ~cmnt:("AbortAU: " ^ Stmt.to_string stmt)
                               ~loc
                               ~spec_error:
                                 (Stmt.mk_const_spec_error error
                                 :: spec.spec_error)
                               (Expr.alpha_renaming spec.spec_form
                                  alpha_renaming_map)))
                  in

                  let inhale_stmt =
                    Stmt.mk_inhale_expr
                      ~cmnt:("AbortAU: " ^ Stmt.to_string stmt)
                      ~loc
                      (Expr.mk_app ~loc ~typ:Type.perm
                         (AUPred opened_au_token.callable)
                         [opened_au_token.token;
                         (Expr.mk_tuple opened_au_token.callable_args)])
                  in

                  let atomicity_state = close_au ~loc token atomicity_state in

                  (exhale_stmts, inhale_stmt, atomicity_state)
              | CommitAU commit_au_desc ->
                  let loc = Stmt.to_loc stmt in

                  let alpha_renaming_map =
                    List.fold2_exn callable_decl.call_decl_returns commit_au_desc.proc_rets
                      ~init:alpha_renaming_map
                      ~f:(fun acc_map formal_arg actual_arg ->
                        Map.add_exn acc_map
                          ~key:(QualIdent.from_ident formal_arg.var_name)
                          ~data:actual_arg)
                  in

                  let exhale_stmts =
                    List.filter_map callable_decl.call_decl_postcond
                      ~f:(fun spec ->
                        if not spec.spec_atomic then None
                        else
                          let error =
                            ( Error.Verification,
                              loc,
                              "An atomic postcondition may not hold at this \
                               commit point." )
                          in
                          Some
                            (Stmt.mk_exhale_expr
                               ~cmnt:("CommitAU: " ^ Stmt.to_string stmt)
                               ~loc
                               ~spec_error:
                                 (Stmt.mk_const_spec_error error
                                 :: spec.spec_error)
                               (Expr.alpha_renaming spec.spec_form
                                  alpha_renaming_map)))
                  in

                  let inhale_stmt =
                    Stmt.mk_inhale_expr
                      ~cmnt:("CommitAU: " ^ Stmt.to_string stmt)
                      ~loc
                      (Expr.mk_app ~loc ~typ:Type.perm
                         (AUPredCommit opened_au_token.callable)
                         ([opened_au_token.token; 
                          (Expr.mk_tuple opened_au_token.callable_args);
                         Expr.mk_tuple commit_au_desc.proc_rets ]))
                  in

                  let atomicity_state = close_au ~loc token atomicity_state in

                  (exhale_stmts, inhale_stmt, atomicity_state)
              | _ -> assert false
            in

            let new_stmt =
              Stmt.mk_block_stmt ~loc (exhale_stmts @ [ inhale_stmt ])
            in

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
          take_ext_step ~loc (ext_hooks.stmt_ext_atomicity stmt_ext)
            atomicity_state
        in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Block { block_kind = Atomic; _ } ->
        (* One step to the enclosing context, however many statements inside. *)
        let outer = take_atomic_step ~loc atomicity_state in
        let* _ =
          Rewriter.set_user_state { outer with in_atomic_block = true }
        in
        let* stmt = Rewriter.Stmt.descend stmt ~f:rewrite_au_cmnds in
        let* inner = Rewriter.current_user_state in
        (* Anything opened inside must be closed inside: an invariant held across
           the block's boundary is held across a step boundary, which is what the
           one-step rule exists to police. *)
        let* () =
          if
            List.length inner.invs_opened <> List.length outer.invs_opened
            || List.length inner.au_opened <> List.length outer.au_opened
          then
            Error.verification_error loc
              "An invariant or atomic update opened inside an atomic block must \
               also be closed inside it"
          else Rewriter.return ()
        in
        let* _ =
          Rewriter.set_user_state
            { inner with in_atomic_block = outer.in_atomic_block }
        in
        Rewriter.return stmt
    | Block block_desc -> Rewriter.Stmt.descend stmt ~f:rewrite_au_cmnds
    | Cond cond_desc ->
        let* then_stmt =
          Rewriter.Stmt.descend cond_desc.cond_then ~f:rewrite_au_cmnds
        in
        let* then_atomicity_state = Rewriter.current_user_state in

        let* _ = Rewriter.set_user_state atomicity_state in
        let* else_stmt =
          Rewriter.Stmt.descend cond_desc.cond_else ~f:rewrite_au_cmnds
        in
        let* else_atomicity_state = Rewriter.current_user_state in

        let if_else_atomicity_states_equal =
          List.length then_atomicity_state.invs_opened
          = List.length else_atomicity_state.invs_opened
          && List.length then_atomicity_state.au_opened
             = List.length else_atomicity_state.au_opened
          && List.for_all2_exn then_atomicity_state.invs_opened
               else_atomicity_state.invs_opened ~f:(fun inv1 inv2 ->
                 QualIdent.equal inv1.inv_name inv2.inv_name
                 && List.for_all2_exn inv1.inv_args inv2.inv_args
                      ~f:Expr.alpha_equal)
          && List.for_all2_exn then_atomicity_state.au_opened
               else_atomicity_state.au_opened ~f:(fun au1 au2 ->
                 Expr.alpha_equal au1.token au2.token
                 && QualIdent.equal au1.callable au2.callable
                 && List.for_all2_exn au1.callable_args au2.callable_args
                      ~f:Expr.alpha_equal
                 && List.for_all2_exn au1.implicit_bound_vars
                      au2.implicit_bound_vars ~f:Expr.alpha_equal)
        in

        if if_else_atomicity_states_equal then
          let new_stmt =
            {
              stmt with
              stmt_desc =
                Cond
                  {
                    cond_desc with
                    cond_then = then_stmt;
                    cond_else = else_stmt;
                  };
            }
          in

          if is_ghost_scope then Rewriter.return new_stmt
          else
            (* [invs_opened]/[au_opened] are required exactly equal above
               (either branch's copy is fine to carry forward). [mask] is
               not: a fresh [fold] in only one branch (see [close_inv]) can
               credit that branch's mask without touching [invs_opened] at
               all, so the two branches' masks can legitimately differ even
               when everything else matches. Only credit established on
               *every* reachable arm is safe to carry past the join -- an
               intersection, not either side alone. *)
            let joined_mask =
              Callable.mask_inter then_atomicity_state.mask
                else_atomicity_state.mask
            in
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
                mask = joined_mask;
                atomic_step_taken =
                  then_atomicity_state.atomic_step_taken
                  || else_atomicity_state.atomic_step_taken;
              }
            in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return new_stmt
        else
          Error.verification_error stmt.stmt_loc
            "Inconsistent atomicity states in then and else branches"
    | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_au_cmnds
  in

  let* stmt = rewrite_au_cmnds stmt in
  let* atomicity_state = Rewriter.current_user_state in

  if
    List.is_empty atomicity_state.au_opened
    && List.is_empty atomicity_state.invs_opened
  then Rewriter.return stmt
  else unclosed_error ~body_loc:stmt.stmt_loc atomicity_state

let rewrite_atomicity_analysis (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  let* scope_id = Rewriter.current_scope_id in
  Logs.debug (fun m ->
      m
        "Rewrites.rewrite_atomicity_analysis: Rewriting atomicity analysis for \
         callable: %a"
        QualIdent.pr scope_id);
  let+ c =
    Rewriter.eval_with_user_state
      ~init:
        {
          au_opened = [];
          invs_opened = [];
          atomic_step_taken = false;
          in_atomic_block = false;
          mask = Option.value c.call_decl.call_decl_needs_mask ~default:[];
        }
      (Rewriter.Callable.rewrite_stmts ~f:rewrite_au_cmnds c)
  in

  c
