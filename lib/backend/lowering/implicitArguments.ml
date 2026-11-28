(** Supplies the implicit ghost arguments of calls from the predicate instances held where
    the call is made, when witness computation could not find them in the state: a
    predicate's ordinary argument is no term of the heap.

    A call that omits an implicit parameter [v] of its callee gets, for [v], the argument
    of the one held instance that agrees with an atom [p(..., v, ...)] of the callee's
    precondition on its other arguments. This is the call with that argument written
    explicitly: the precondition is checked for it as for any other argument. Instances
    are held from the procedure's preconditions, inhales, folds and the postconditions of
    calls, until an exhale, unfold or call precondition consumes them or an assignment
    changes a variable they mention; they are tracked through blocks and branches, but not
    into or out of loops and extension statements, like the instances that unfolds open
    (see [Lowering.track_unfolds]). *)

open Base
open Ast

type held = {
  pred : string;  (** The resolved predicate. *)
  args : Expr.t list;
  spellings : string list;  (** The arguments, as compared. *)
  mentions : (Ident.t, Ident.comparator_witness) Set.t;
}

let same left right =
  String.equal left.pred right.pred
  && List.equal String.equal left.spellings right.spellings

let make_held pred args =
  {
    pred;
    args;
    spellings = List.map args ~f:Expr.to_string;
    mentions =
      List.fold args
        ~init:(Set.empty (module Ident))
        ~f:(fun mentions arg -> Set.union mentions (Expr.local_vars arg));
  }

(** The conjuncts of [expr] outside any binder, conditional or implication. *)
let rec conjuncts (expr : Expr.t) =
  match expr with
  | App (And, args, _) -> List.concat_map args ~f:conjuncts
  | _ -> [ expr ]

(** The predicate or invariant that [expr] is an instance of, resolved, with its
    arguments. *)
let atom (expr : Expr.t) : (string * Expr.t list) option Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | App (Var name, (_ :: _ as args), _) ->
      let+ found = Rewriter.resolve_and_find_opt name in
      Option.bind found ~f:(fun (resolved, symbol) ->
          match Rewriter.Symbol.orig_symbol symbol with
          | CallDef { call_decl = { call_decl_kind = Pred | Invariant; _ }; _ } ->
              Some (QualIdent.to_string resolved, args)
          | _ -> None)
  | _ -> Rewriter.return None

(** The instances that [specs] hold, after [renaming]. *)
let instances renaming (specs : Stmt.spec list) =
  let open Rewriter.Syntax in
  let+ atoms =
    Rewriter.List.map
      (List.concat_map specs ~f:(fun spec ->
           conjuncts (Expr.alpha_renaming spec.Stmt.spec_form renaming)))
      ~f:atom
  in
  List.filter_map atoms ~f:(Option.map ~f:(fun (pred, args) -> make_held pred args))

let gain gained held =
  gained @ List.filter held ~f:(fun h -> not (List.exists gained ~f:(same h)))

(** [held] without one instance of each of [consumed]. *)
let consume consumed held =
  List.fold consumed ~init:held ~f:(fun held c ->
      let rec drop = function
        | [] -> []
        | h :: rest -> if same h c then rest else h :: drop rest
      in
      drop held)

let invalidate assigned held =
  List.filter held ~f:(fun h -> not (List.exists assigned ~f:(Set.mem h.mentions)))

let variable_of (vd : Type.var_decl) (expr : Expr.t) =
  match expr with
  | App (Var name, [], _) -> Ident.equal (QualIdent.unqualify name) vd.var_name
  | _ -> false

(** The argument for the omitted implicit parameter [v], given [renaming] of the callee's
    supplied parameters, if one held instance determines it. *)
let candidate held renaming ~omitted (precond : Stmt.spec list) (v : Type.var_decl) =
  let open Rewriter.Syntax in
  let mentions_omitted arg =
    List.exists omitted ~f:(fun (o : Type.var_decl) ->
        Set.mem (Expr.local_vars arg) o.var_name)
  in
  let forms =
    List.concat_map precond ~f:(fun spec ->
        conjuncts (Expr.alpha_renaming spec.Stmt.spec_form renaming))
  in
  (* A parameter the state may determine, through own, is left to witness computation. *)
  let owned =
    List.exists forms ~f:(fun form ->
        match form with
        | App (Own, args, _) ->
            List.exists args ~f:(fun arg -> Set.mem (Expr.local_vars arg) v.var_name)
        | _ -> false)
  in
  if owned then Rewriter.return None
  else
    let+ atoms = Rewriter.List.map forms ~f:atom in
    let candidates =
      List.concat_map (List.filter_opt atoms) ~f:(fun (pred, args) ->
          match List.findi args ~f:(fun _ arg -> variable_of v arg) with
          | None -> []
          | Some (position, _) ->
              let others = List.filteri args ~f:(fun i _ -> i <> position) in
              if List.exists others ~f:mentions_omitted then []
              else
                let spellings = List.map others ~f:Expr.to_string in
                List.filter_map held ~f:(fun h ->
                    let held_others =
                      List.filteri h.spellings ~f:(fun i _ -> i <> position)
                    in
                    if
                      String.equal h.pred pred
                      && List.length h.args = List.length args
                      && List.equal String.equal held_others spellings
                    then Some (List.nth_exn h.args position)
                    else None))
    in
    match
      List.dedup_and_sort candidates ~compare:(fun a b ->
          String.compare (Expr.to_string a) (Expr.to_string b))
    with
    | [ argument ] -> Some argument
    | _ -> None

(** [call_desc] with the omitted implicit arguments that [held] determines, and the
    instances held after the call. *)
let call held (stmt : Stmt.t) (call_desc : Stmt.call_desc) =
  let open Rewriter.Syntax in
  let* callee = Rewriter.resolve_and_find_opt call_desc.call_name in
  let procedure =
    Option.bind callee ~f:(fun (_, symbol) ->
        match Rewriter.Symbol.orig_symbol symbol with
        | CallDef { call_decl = { call_decl_kind = Proc | Lemma; _ }; _ } -> Some symbol
        | _ -> None)
  in
  match procedure with
  | Some symbol when not call_desc.call_is_spawn ->
      let* call_decl = Rewriter.Symbol.reify_callable_decl symbol in
      let formals = call_decl.call_decl_formals in
      let supplied, omitted = List.split_n formals (List.length call_desc.call_args) in
      let renaming_of pairs =
        List.fold pairs
          ~init:(Map.empty (module QualIdent))
          ~f:(fun renaming ((formal : Type.var_decl), arg) ->
            Map.set renaming ~key:(QualIdent.from_ident formal.var_name) ~data:arg)
      in
      let renaming = renaming_of (List.zip_exn supplied call_desc.call_args) in
      (* The omitted parameters are implicit and trailing: a prefix of them can be given. *)
      let rec fill renaming found = function
        | [] -> Rewriter.return (renaming, List.rev found)
        | (v : Type.var_decl) :: rest when v.var_implicit -> (
            let* argument =
              candidate held renaming ~omitted:(v :: rest) call_decl.call_decl_precond v
            in
            match argument with
            | Some argument ->
                fill
                  (Map.set renaming ~key:(QualIdent.from_ident v.var_name) ~data:argument)
                  (argument :: found) rest
            | None -> Rewriter.return (renaming, List.rev found))
        | _ -> Rewriter.return (renaming, List.rev found)
      in
      let* renaming, found = fill renaming [] omitted in
      let call_desc = { call_desc with call_args = call_desc.call_args @ found } in
      let complete = List.length call_desc.call_args = List.length formals in
      let* consumed = instances renaming call_decl.call_decl_precond in
      let held = consume consumed held in
      let assigned = List.map call_desc.call_lhs ~f:QualIdent.unqualify in
      let held = invalidate assigned held in
      let* held =
        if not complete then Rewriter.return held
        else
          let returns, lhs =
            ( List.take call_decl.call_decl_returns (List.length call_desc.call_lhs),
              call_desc.call_lhs )
          in
          let renaming =
            List.fold (List.zip_exn returns lhs) ~init:renaming
              ~f:(fun renaming ((r : Type.var_decl), x) ->
                Map.set renaming
                  ~key:(QualIdent.from_ident r.var_name)
                  ~data:(Expr.mk_var ~typ:r.var_type x))
          in
          let dropped =
            List.drop call_decl.call_decl_returns (List.length call_desc.call_lhs)
          in
          let+ gained = instances renaming call_decl.call_decl_postcond in
          let gained =
            List.filter gained ~f:(fun h ->
                not
                  (List.exists dropped ~f:(fun (r : Type.var_decl) ->
                       Set.mem h.mentions r.var_name)))
          in
          gain gained held
      in
      Rewriter.return ({ stmt with stmt_desc = Basic (Call call_desc) }, held)
  | _ ->
      let assigned = List.map call_desc.call_lhs ~f:QualIdent.unqualify in
      Rewriter.return (stmt, invalidate assigned held)

let empty_renaming = Map.empty (module QualIdent)

(** The variables [stmt] assigns, if it is a basic statement. *)
let assigned_vars (stmt : Stmt.t) : Ident.t list =
  let idents = List.map ~f:QualIdent.unqualify in
  match stmt.stmt_desc with
  | Basic (Assign { assign_lhs; _ }) -> idents assign_lhs
  | Basic (Bind { bind_lhs; _ }) -> idents bind_lhs
  | Basic (Havoc { havoc_var; _ }) -> idents [ havoc_var ]
  | Basic (Call { call_lhs; _ }) -> idents call_lhs
  | Basic (New { new_lhs; _ }) -> idents [ new_lhs ]
  | Basic (FieldRead { field_read_lhs; _ }) -> idents [ field_read_lhs ]
  | Basic (AUAction { auaction_kind = OpenAU { lhs; _ } }) ->
      List.concat_map lhs ~f:(fun e -> Set.to_list (Expr.local_vars e))
  | _ -> []

(** [stmt] with the implicit arguments of its calls supplied, given the instances [held]
    before it, and those held after it. *)
let rec track (held : held list) (stmt : Stmt.t) : (Stmt.t * held list) Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Block block ->
      let+ held, body =
        Rewriter.List.fold_left block.block_body ~init:(held, [])
          ~f:(fun (held, body) s ->
            let+ s, held = track held s in
            (held, s :: body))
      in
      ({ stmt with stmt_desc = Block { block with block_body = List.rev body } }, held)
  | Cond cond ->
      let* cond_then, after_then = track held cond.cond_then in
      let+ cond_else, after_else = track held cond.cond_else in
      let joined =
        if cond.cond_if_assumes_false then after_else
        else List.filter after_then ~f:(fun h -> List.exists after_else ~f:(same h))
      in
      ({ stmt with stmt_desc = Cond { cond with cond_then; cond_else } }, joined)
  | Basic (Call call_desc) -> call held stmt call_desc
  | Basic (Use use_desc) ->
      let* atom =
        atom (Expr.mk_app ~typ:Type.perm (Var use_desc.use_name) use_desc.use_args)
      in
      let instance = Option.map atom ~f:(fun (pred, args) -> make_held pred args) in
      let held =
        match (use_desc.use_kind, instance) with
        | Fold, Some instance -> gain [ instance ] held
        | Unfold, Some instance -> consume [ instance ] held
        | _, None -> held
      in
      Rewriter.return (stmt, held)
  | Basic (Spec (Inhale, spec)) ->
      let+ gained = instances empty_renaming [ spec ] in
      (stmt, gain gained held)
  | Basic (Spec (Exhale, spec)) ->
      let+ consumed = instances empty_renaming [ spec ] in
      (stmt, consume consumed held)
  | Basic (Spec (Cut, _)) -> Rewriter.return (stmt, [])
  | Basic _ -> Rewriter.return (stmt, invalidate (assigned_vars stmt) held)
  | Loop _ | StmtExt _ ->
      let+ stmt =
        Rewriter.Stmt.descend stmt ~f:(fun s ->
            let+ s, _ = track [] s in
            s)
      in
      (stmt, [])

(** [callable] with the implicit arguments of its calls supplied where its preconditions
    and the instances held along the way determine them. *)
let rewrite_callable (callable : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  let* held = instances empty_renaming callable.call_decl.call_decl_precond in
  Rewriter.Callable.rewrite_stmts callable ~f:(fun body ->
      let+ body, _ = track held body in
      body)
