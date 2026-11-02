open Base
open Raven
open Ast

let variable name typ =
  Expr.mk_var ~typ (QualIdent.from_list [ Ident.make Util.Loc.dummy name 0 ])

let check expression =
  let rec visit = function
    | [] -> ()
    | (Expr.App ((And | Or), [ left; right ], _) as expression) :: rest ->
        assert (
          Type.equal (Expr.to_type expression)
            (Type.join (Expr.to_type left) (Expr.to_type right)));
        visit (left :: right :: rest)
    | Expr.App ((And | Or), _, _) :: _ -> assert false
    | Expr.App (_, arguments, _) :: rest -> visit (arguments @ rest)
    | Expr.Binder (_, _, triggers, body, _) :: rest ->
        visit ((body :: List.concat triggers) @ rest)
  in
  visit [ expression ]

let operands operator expression =
  let rec collect found = function
    | [] -> List.rev found
    | Expr.App (actual, [ left; right ], _) :: rest when Expr.equal_constr operator actual
      ->
        collect found (left :: right :: rest)
    | expression :: rest -> collect (expression :: found) rest
  in
  collect [] [ expression ]

let () =
  let values = List.init 4 ~f:(fun i -> variable (Int.to_string i) Type.bool) in
  List.iter [ Expr.And; Expr.Or ] ~f:(fun operator ->
      let make = match operator with Expr.And -> Expr.mk_and | _ -> Expr.mk_or in
      let empty = make [] in
      begin match empty with
      | Expr.App (Bool value, [], _) ->
          assert (Bool.equal value (Expr.equal_constr operator And))
      | _ -> assert false
      end;
      List.iter [ 1; 2; 4 ] ~f:(fun length ->
          let inputs = List.take values length in
          let expression = make inputs in
          check expression;
          assert (
            List.equal
              (fun a b -> Expr.compare a b = 0)
              inputs
              (operands operator expression)));
      check (Expr.mk_app ~typ:Type.bool operator values));
  let mixed = values @ [ variable "resource" Type.perm ] in
  let conjunction = Expr.mk_and mixed in
  check conjunction;
  assert (Type.equal (Expr.to_type conjunction) Type.perm);
  check (Expr.mk_or mixed);
  let simplified =
    Expr.drop_trivially_true
      (Expr.mk_and [ Expr.mk_bool true; Expr.mk_and values; Expr.mk_bool true ])
  in
  check simplified;
  assert (List.equal (fun a b -> Expr.compare a b = 0) values (operands And simplified))
