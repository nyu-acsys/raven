open Base
open Raven
open Ast

let loc = Util.Loc.dummy
let id name = Ident.make loc name 0
let qi names = QualIdent.from_list (List.map names ~f:id)
let decl name = Type.mk_var_decl ~loc (id name) Type.int
let use name = Expr.from_var_decl (decl name)
let unchanged context _ variables = (context, variables)

let expression =
  let trigger =
    Expr.mk_app ~typ:Type.int (Var (qi [ "tag" ])) [ use "bound"; use "trigger_only" ]
  in
  Expr.mk_binder ~trigs:[ [ trigger ] ] Forall
    [ decl "bound" ]
    (Expr.mk_eq (use "bound") (use "free"))

(* A fold's result can be a scalar rather than an expression. *)
let count ?stop ?include_triggers expression =
  Expr.map ?stop ?include_triggers ~enter:unchanged
    ~app:(fun () _ children _ -> 1 + List.fold children ~init:0 ~f:( + ))
    ~binder:(fun () _ _ triggers body _ ->
      1 + body + List.fold (List.concat triggers) ~init:0 ~f:( + ))
    () expression

let () =
  assert (count expression = 7);
  assert (count ~include_triggers:false expression = 4);
  let stop () = function Expr.App (Eq, _, _) -> Some 100 | _ -> None in
  assert (count ~stop expression = 104)

(* The accumulator crosses siblings; lexical bindings remain local. *)
let () =
  let enter bound trace _ variables =
    let inner =
      List.fold variables ~init:bound ~f:(fun bound variable ->
          Set.add bound (QualIdent.from_ident variable.Type.var_name))
    in
    (inner, "enter" :: trace, variables)
  in
  let app bound trace constr children _ =
    let trace =
      match constr with
      | Expr.Var name ->
          let scope = if Set.mem bound name then "bound:" else "free:" in
          (scope ^ Ident.name (QualIdent.unqualify name)) :: trace
      | _ -> trace
    in
    (trace, 1 + List.fold children ~init:0 ~f:( + ))
  in
  let binder bound trace _ _ triggers body _ =
    assert (Set.is_empty bound);
    ("leave" :: trace, 1 + body + List.fold (List.concat triggers) ~init:0 ~f:( + ))
  in
  let trace, nodes =
    Expr.fold_map ~enter ~app ~binder
      (Set.empty (module QualIdent))
      []
      (Expr.mk_tuple [ expression; use "bound" ])
  in
  assert (nodes = 9);
  assert (
    List.equal String.equal (List.rev trace)
      [
        "enter";
        "bound:bound";
        "free:trigger_only";
        "free:tag";
        "bound:bound";
        "free:free";
        "leave";
        "free:bound";
      ])

(* Lexical context reaches both triggers and body without escaping to siblings. *)
let () =
  let combine sets = List.fold sets ~init:(Set.empty (module QualIdent)) ~f:Set.union in
  let enter bound _ variables =
    ( List.fold variables ~init:bound ~f:(fun bound variable ->
          Set.add bound (QualIdent.from_ident variable.Type.var_name)),
      variables )
  in
  let free =
    Expr.map ~enter
      ~app:(fun bound constr children _ ->
        let names = combine children in
        match constr with
        | Var name when not (Set.mem bound name) -> Set.add names name
        | _ -> names)
      ~binder:(fun _ _ _ triggers body _ -> combine (body :: List.concat triggers))
      (Set.empty (module QualIdent))
      expression
  in
  assert (
    Set.equal free
      (Set.of_list
         (module QualIdent)
         [ qi [ "tag" ]; qi [ "trigger_only" ]; qi [ "free" ] ]));
  let signature = Expr.signature expression in
  assert (List.equal QualIdent.equal (Map.keys signature) [ qi [ "free" ] ]);
  assert (
    Set.equal
      (Expr.mentioned_vars (Set.empty (module Ident)) expression)
      (Set.of_list
         (module Ident)
         (List.map [ "tag"; "bound"; "trigger_only"; "free" ] ~f:id)))

(* Identifier-only and fully qualified mapping retain their different metadata policies. *)
let () =
  let old_name = qi [ "Types"; "Old" ] in
  let new_name = qi [ "Types"; "New" ] in
  let old_type = Type.mk_var old_name in
  let new_type = Type.mk_var new_name in
  let variable = { (decl "bound") with var_type = old_type } in
  let value = Expr.set_type_annot (Expr.from_var_decl variable) (Some old_type) in
  let original =
    Expr.mk_binder ~trigs:[ [ value ] ] Forall [ variable ] (Expr.mk_eq value value)
  in
  let rename name = if QualIdent.equal name old_name then new_name else name in
  assert (Poly.equal (Expr.map_idents rename original) original);
  match Expr.map_qual_idents ~f:rename original with
  | Expr.Binder (_, [ variable ], [ [ trigger ] ], Expr.App (Eq, values, _), _) ->
      assert (Ident.equal variable.var_name (id "bound"));
      assert (Type.equal variable.var_type new_type);
      List.iter (trigger :: values) ~f:(fun value ->
          assert (Type.equal (Expr.to_type value) new_type);
          assert (Option.equal Type.equal (Expr.to_type_annot value) (Some new_type)))
  | _ -> failwith "expected unchanged expression shape"
