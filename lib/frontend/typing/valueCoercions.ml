open Base
open Ast
open Util
open Rewriter.Syntax

let rec equal_representation source target =
  match (source, target) with
  | Type.App (FinSet, [ source ], _), Type.App (Map, [ target; bool ], _)
  | Type.App (Map, [ source; bool ], _), Type.App (FinSet, [ target ], _) ->
      Type.equal bool Type.bool && equal_representation source target
  | Type.App (source, sources, _), Type.App (target, targets, _) ->
      Int.equal (Type.compare_constr source target) 0
      && equal_representations sources targets

and equal_representations sources targets =
  match (sources, targets) with
  | [], [] -> true
  | source :: sources, target :: targets ->
      equal_representation source target && equal_representations sources targets
  | _ -> false

let same_representation source target =
  if equal_representation source target then Rewriter.return true
  else
    let+ source = TypeExpr.expand_type_expr source
    and+ target = TypeExpr.expand_type_expr target in
    equal_representation source target

(* Inference placeholders constrain checking, but do not request a representation. *)
let rec contextual_type source target =
  match (source, target) with
  | _, Type.App ((Any | Bot | Num | Perm), [], _) -> source
  | Type.App ((Map | FinSet), _, _), Type.App (Map, [ domain; range ], attr) ->
      Type.App
        ( Map,
          [
            contextual_type (Type.map_dom source) domain;
            contextual_type (Type.map_codom source) range;
          ],
          attr )
  | Type.App ((Map | FinSet), _, _), Type.App (FinSet, [ domain ], attr) ->
      Type.App (FinSet, [ contextual_type (Type.map_dom source) domain ], attr)
  | Type.App (Prod, sources, _), Type.App (Prod, targets, attr) ->
      begin match List.map2 sources targets ~f:contextual_type with
      | Ok targets -> Type.App (Prod, targets, attr)
      | Unequal_lengths -> target
      end
  | _ -> target

(* Both types are expanded by the checker before reaching this entry point. *)
let rec coerce_expanded expr target =
  let source = Expr.to_type expr in
  if equal_representation source target then Rewriter.return expr
  else
    let target = contextual_type source target in
    if equal_representation source target then Rewriter.return expr
    else
      let loc = Expr.to_loc expr in
      let target = Type.set_ghost (Type.is_ghost source) target in
      match (source, target) with
      | Type.App (Int, [], _), Type.App (Real, [], _) ->
          Rewriter.return (Expr.mk_to_real ~loc expr)
      | Type.App ((Map | FinSet), _, _), Type.App ((Map | FinSet), _, _) ->
          let domain = Type.map_dom target in
          let variable = Type.mk_var_decl (Ident.fresh loc "coerce_index") domain in
          let* index =
            coerce_expanded (Expr.from_var_decl variable) (Type.map_dom source)
          in
          let value =
            Expr.mk_app ~loc ~typ:(Type.map_codom source) MapLookUp [ expr; index ]
          in
          let+ body = coerce_expanded value (Type.map_codom target) in
          Expr.mk_binder ~loc ~typ:target Compr [ variable ] body
      | Type.App (Prod, sources, _), Type.App (Prod, targets, _)
        when List.length sources = List.length targets ->
          let+ elements =
            Rewriter.List.map
              (List.mapi targets ~f:(fun index target -> (index, target)))
              ~f:(fun (index, target) ->
                coerce_expanded (Expr.mk_tuple_lookup ~loc expr index) target)
          in
          Expr.mk_app ~loc ~typ:target Tuple elements
      | _ ->
          Error.internal_error loc
            (Printf.sprintf
               !"Unsupported value coercion from %{Type} to %{Type}"
               source target)

let coerce expr target =
  if equal_representation (Expr.to_type expr) target then Rewriter.return expr
  else
    let* source = TypeExpr.expand_type_expr (Expr.to_type expr)
    and* target = TypeExpr.expand_type_expr target in
    coerce_expanded (Expr.set_type expr source) target
