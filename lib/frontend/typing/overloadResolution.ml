open Base
open Ast

type formal = { type_ : Type.t; ghost : bool; implicit : bool }

type candidate = {
  identity : QualIdent.t;
  kind : Callable.call_kind;
  ghost : bool;
  parameters : formal list;
  returns : Type.t;
  generic_parameters : QualIdent.t list;
}

type evidence_type = Known of Type.t | Literal of Type.t | Unknown
type evidence = { type_ : evidence_type; ghost : bool }
type bindings = (QualIdent.t * Type.t) list

type solution = {
  candidate : candidate;
  bindings : bindings;
  parameter_types : Type.t list;
  return_type : Type.t;
}

type mismatch = Kind | Arity | Ghost | Conflicting_binding of QualIdent.t | Argument

type applicability =
  | Applicable of solution
  | Underdetermined of solution
  | Mismatch of mismatch

type resolution =
  | Selected of solution
  | Ambiguous of solution list
  | Deferred of solution list
  | No_match of (QualIdent.t * mismatch) list

(* Extract signatures without reifying bodies. Normalize requalified types before matching. *)
let of_symbol ~identity ~generic_parameters symbol =
  Rewriter.Symbol.extract symbol ~f:(fun _ requalify symbol ->
      let rec type_ (Type.App (head, args, attr)) =
        let head =
          match head with
          | Type.Var qi -> Type.Var (requalify qi)
          | Type.AtomicToken qi -> Type.AtomicToken (requalify qi)
          | Type.Data (qi, variants) -> Type.Data (requalify qi, variants)
          | head -> head
        in
        Type.App (head, List.map args ~f:type_, attr)
      in
      match symbol with
      | Module.CallDef callable ->
          let decl = callable.call_decl in
          Some
            {
              identity;
              generic_parameters = List.map generic_parameters ~f:requalify;
              kind = decl.call_decl_kind;
              ghost = Callable.is_ghost_kind decl.call_decl_kind;
              parameters =
                List.map decl.call_decl_formals ~f:(fun p ->
                    {
                      type_ = type_ p.var_type;
                      ghost = p.var_ghost || Type.is_ghost p.var_type;
                      implicit = p.var_implicit;
                    });
              returns =
                Type.mk_prod Util.Loc.dummy
                  (List.map decl.call_decl_returns ~f:(fun p -> type_ p.var_type));
            }
      | _ -> None)

(* Signatures are expanded by the caller; comparison ignores source attributes. *)
let rec normalize (Type.App (head, args, _)) =
  Type.App (head, List.map args ~f:normalize, Type.dummy_attr)

let rec substitute bindings (Type.App (head, args, _) as tp) =
  match (head, args) with
  | Type.Var qi, [] ->
      Option.value (List.Assoc.find bindings qi ~equal:QualIdent.equal) ~default:tp
  | _ -> Type.App (head, List.map args ~f:(substitute bindings), Type.dummy_attr)

let rec contains_generic candidate (Type.App (head, args, _)) =
  (match head with
    | Type.Var qi -> List.mem candidate.generic_parameters qi ~equal:QualIdent.equal
    | _ -> false)
  || List.exists args ~f:(contains_generic candidate)

let partial_subtype candidate left right =
  let wildcard = function
    | Type.App (Var qi, [], _) ->
        List.mem candidate.generic_parameters qi ~equal:QualIdent.equal
    | _ -> false
  in
  let rec subtype left right =
    if wildcard left || wildcard right then true
    else if not (contains_generic candidate left || contains_generic candidate right) then
      Type.subtype_of left right
    else
      match (left, right) with
      | Type.App (Bot, [], _), _ | _, Type.App (Any, [], _) -> true
      | Type.App (Map, [ ld; lr ], _), Type.App (Map, [ rd; rr ], _) ->
          subtype rd ld && subtype lr rr
      | Type.App (FinSet, [ left ], _), Type.App (FinSet, [ right ], _)
      | ( Type.App (FinSet, [ left ], _),
          Type.App (Map, [ right; Type.App (Bool, [], _) ], _) ) ->
          subtype right left
      | Type.App (Prod, left, _), Type.App (Prod, right, _) ->
          begin match List.zip left right with
          | Ok pairs -> List.for_all pairs ~f:(fun (left, right) -> subtype left right)
          | Unequal_lengths -> false
          end
      | Type.App (Fld, [ left ], _), Type.App (Fld, [ right ], _) ->
          subtype left right && subtype right left
      | _ -> false
  in
  subtype left right

let rec uncertain (Type.App (head, args, _)) =
  (match head with Type.Bot | Any | Num -> true | _ -> false)
  || List.exists args ~f:uncertain

let rec contextual_literal actual formal =
  match (actual, formal) with
  | Type.App (Bot, [], _), _ -> formal
  | ( Type.App (FinSet, [ element ], attr),
      Type.App (Map, [ expected; Type.App (Bool, [], _) ], _) ) ->
      Type.App (FinSet, [ contextual_literal element expected ], attr)
  | Type.App (head, args, attr), Type.App (expected_head, expected_args, _)
    when Type.equal (Type.mk_app head []) (Type.mk_app expected_head []) ->
      begin match List.zip args expected_args with
      | Ok pairs ->
          Type.App (head, List.map pairs ~f:(fun (a, e) -> contextual_literal a e), attr)
      | Unequal_lengths -> actual
      end
  | _ -> actual

let infer candidate ~only_unbound bindings formal actual =
  let rec go bindings formal actual =
    match (formal, actual) with
    | Type.App (Var qi, [], _), _
      when List.mem candidate.generic_parameters qi ~equal:QualIdent.equal ->
        if uncertain actual then Ok bindings
        else
          begin match List.Assoc.find bindings qi ~equal:QualIdent.equal with
          | Some prior when (not only_unbound) && not (Type.equal prior actual) ->
              Error (Conflicting_binding qi)
          | Some _ -> Ok bindings
          | None -> Ok ((qi, actual) :: bindings)
          end
    | ( Type.App (Map, [ element; Type.App (Bool, [], _) ], _),
        Type.App (FinSet, [ actual ], _) )
    | ( Type.App (FinSet, [ element ], _),
        Type.App (Map, [ actual; Type.App (Bool, [], _) ], _) ) ->
        go bindings element actual
    | Type.App (head, args, _), Type.App (actual_head, actual_args, _)
      when Type.equal (Type.mk_app head []) (Type.mk_app actual_head []) ->
        begin match List.zip args actual_args with
        | Unequal_lengths -> Ok bindings
        | Ok pairs ->
            List.fold_result pairs ~init:bindings ~f:(fun bindings (formal, actual) ->
                go bindings formal actual)
        end
    | _ -> Ok bindings
  in
  go bindings formal actual

let match_candidate ?expected ~ghost_context candidate arguments =
  let supplied = List.length arguments in
  let formals = List.take candidate.parameters supplied in
  if not (Callable.compare_call_kind candidate.kind Callable.Func = 0) then Mismatch Kind
  else if
    supplied > List.length candidate.parameters
    || not
         (List.for_all (List.drop candidate.parameters supplied) ~f:(fun p -> p.implicit))
  then Mismatch Arity
  else if candidate.ghost && not ghost_context then Mismatch Ghost
  else begin
    let pairs =
      match List.zip formals arguments with Ok pairs -> pairs | Unequal_lengths -> []
    in
    if
      List.exists pairs ~f:(fun ((p : formal), (a : evidence)) ->
          a.ghost && not (ghost_context || p.ghost))
    then Mismatch Ghost
    else
      let inferred =
        List.fold_result pairs ~init:[] ~f:(fun bindings (formal, argument) ->
            match argument.type_ with
            | Unknown -> Ok bindings
            | Known tp | Literal tp ->
                infer candidate ~only_unbound:false bindings (normalize formal.type_)
                  (normalize tp))
      in
      let inferred =
        Result.bind inferred ~f:(fun bindings ->
            match expected with
            | None -> Ok bindings
            | Some tp ->
                infer candidate ~only_unbound:true bindings (normalize candidate.returns)
                  (normalize tp))
      in
      match inferred with
      | Error reason -> Mismatch reason
      | Ok bindings ->
          let parameter_types =
            List.map formals ~f:(fun p -> substitute bindings (normalize p.type_))
          in
          let solution =
            {
              candidate;
              bindings;
              parameter_types;
              return_type = substitute bindings (normalize candidate.returns);
            }
          in
          let unresolved =
            List.exists arguments ~f:(fun argument ->
                match argument.type_ with Unknown -> true | Known _ | Literal _ -> false)
            || List.exists candidate.generic_parameters ~f:(fun qi ->
                not (List.Assoc.mem bindings qi ~equal:QualIdent.equal))
          in
          let compatible =
            List.for_all pairs ~f:(fun (original, argument) ->
                let formal = substitute bindings (normalize original.type_) in
                match argument.type_ with
                | Unknown -> true
                | Known tp -> partial_subtype candidate (normalize tp) formal
                | Literal tp ->
                    partial_subtype candidate
                      (contextual_literal (normalize tp) formal)
                      formal)
          in
          if not compatible then Mismatch Argument
          else if unresolved then Underdetermined solution
          else Applicable solution
  end

let more_specific left right =
  let pointwise left right =
    match List.zip left right with
    | Unequal_lengths -> false
    | Ok pairs -> List.for_all pairs ~f:(fun (left, right) -> Type.subtype_of left right)
  in
  pointwise left.parameter_types right.parameter_types
  && not (pointwise right.parameter_types left.parameter_types)

let resolve ?expected ~ghost_context candidates arguments =
  let candidates =
    List.dedup_and_sort candidates ~compare:(fun a b ->
        QualIdent.compare a.identity b.identity)
  in
  let applicable, unresolved, rejected =
    List.fold candidates ~init:([], [], [])
      ~f:(fun (applicable, unresolved, rejected) candidate ->
        match match_candidate ?expected ~ghost_context candidate arguments with
        | Applicable solution -> (solution :: applicable, unresolved, rejected)
        | Underdetermined solution -> (applicable, solution :: unresolved, rejected)
        | Mismatch reason ->
            (applicable, unresolved, (candidate.identity, reason) :: rejected))
  in
  if not (List.is_empty unresolved) then
    Deferred (List.rev_append unresolved (List.rev applicable))
  else
    match
      List.filter applicable ~f:(fun candidate ->
          not (List.exists applicable ~f:(fun other -> more_specific other candidate)))
    with
    | [] -> No_match (List.rev rejected)
    | [ solution ] -> Selected solution
    | solutions -> Ambiguous (List.rev solutions)
