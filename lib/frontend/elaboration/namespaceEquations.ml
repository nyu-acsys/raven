open Base
open Util
open AstDef
module DependencyGraph = Graph.Make (QualIdent)

type t = {
  declarations : NamespaceContract.namespace_decl list;
  by_name : NamespaceContract.namespace_decl Map.M(QualIdent).t;
  required_upper_bounds : Callable.mask Map.M(QualIdent).t;
}

let declarations equations = equations.declarations
let upper_bound equations name = Map.find equations.required_upper_bounds name

let instantiate formals actual_args mask =
  let supplied = Int.min (List.length formals) (List.length actual_args) in
  let renaming =
    List.fold2_exn (List.take formals supplied)
      (List.take actual_args supplied)
      ~init:(Map.empty (module QualIdent))
      ~f:(fun renaming formal actual ->
        Map.set renaming ~key:(QualIdent.from_ident formal.Type.var_name) ~data:actual)
  in
  let supplied_formals =
    List.take formals supplied
    |> List.map ~f:(fun formal -> formal.Type.var_name)
    |> Set.of_list (module Ident)
  in
  List.map mask ~f:(fun (head, args) ->
      (* Project before substitution: an omitted formal may share a caller's name. *)
      let args =
        List.take_while args ~f:(fun arg ->
            Set.is_subset (Expr.local_vars arg) ~of_:supplied_formals)
      in
      (head, List.map args ~f:(fun arg -> Expr.alpha_renaming arg renaming)))
  |> Callable.mask_canon

let expand by_name upper_bounds mask =
  List.concat_map mask ~f:(fun ((head, args) as entry) ->
      match head with
      | Callable.MaskHead.Invariant _ -> [ entry ]
      | Dependencies name ->
          begin match (Map.find by_name name, Map.find upper_bounds name) with
          | Some (declaration : NamespaceContract.namespace_decl), Some bound ->
              instantiate declaration.NamespaceContract.formals args bound
          | _ -> [ entry ]
          end)
  |> Callable.mask_canon

(** Upper bounds are safe for required masks, never for masks granted by a contract. *)
let expand_required equations mask =
  expand equations.by_name equations.required_upper_bounds mask

(** Normalize aliases exposed by expansion; widening applies only to requirements. *)
let normalize_required ~resolve equations mask =
  let open State.Syntax in
  let rec normalize seen mask =
    let* resolved = resolve mask in
    let expanded = expand_required equations resolved in
    let* resolved = resolve expanded in
    if Callable.mask_equal mask resolved then State.return resolved
    else
      let next =
        List.map resolved ~f:(fun ((head, _) as entry) ->
            let previous =
              List.filter seen ~f:(fun (other, _) -> Callable.equal_mask_head head other)
            in
            if
              (not (List.is_empty previous))
              && not
                   (List.exists previous ~f:(fun old ->
                        Callable.compare_mask_entry old entry = 0))
            then (head, [])
            else entry)
        |> Callable.mask_canon
      in
      if Callable.mask_equal mask next then State.return next
      else normalize (Callable.mask_union seen mask) next
  in
  normalize [] mask

let solve declarations =
  let by_name =
    Map.of_alist_exn
      (module QualIdent)
      (List.map declarations ~f:(fun declaration ->
           (declaration.NamespaceContract.name, declaration)))
  in
  let graph =
    Map.fold by_name ~init:DependencyGraph.empty ~f:(fun ~key ~data:_ graph ->
        DependencyGraph.add_vertex graph key)
  in
  let graph =
    Map.fold by_name ~init:graph ~f:(fun ~key ~data:declaration graph ->
        match declaration.definition with
        | Abstract -> graph
        | Defined body ->
            List.fold body ~init:graph ~f:(fun graph (head, _) ->
                match head with
                | Callable.MaskHead.Dependencies dependency
                  when Map.mem by_name dependency ->
                    DependencyGraph.add_edge graph key dependency
                | Invariant _ | Dependencies _ -> graph))
  in
  let bound upper_bounds name =
    let declaration = Map.find_exn by_name name in
    match declaration.definition with
    | Abstract ->
        [
          ( Callable.MaskHead.Dependencies name,
            List.map declaration.formals ~f:Expr.from_var_decl );
        ]
    | Defined body -> expand by_name upper_bounds body
  in
  let solve_component upper_bounds component =
    match component with
    | [] -> upper_bounds
    | [ name ] when not (Set.mem (DependencyGraph.succs graph name) name) ->
        Map.set upper_bounds ~key:name ~data:(bound upper_bounds name)
    | _ ->
        let initial =
          List.fold component ~init:upper_bounds ~f:(fun bounds name ->
              Map.set bounds ~key:name ~data:[])
        in
        (* Recursive argument transformations may produce infinitely many prefixes. *)
        let rec fixed_point previous =
          let next =
            List.fold component ~init:previous ~f:(fun next name ->
                let widened =
                  bound previous name
                  |> List.map ~f:(fun (head, _) -> (head, []))
                  |> Callable.mask_canon
                in
                Map.set next ~key:name
                  ~data:(Callable.mask_union (Map.find_exn previous name) widened))
          in
          if
            List.for_all component ~f:(fun name ->
                Callable.mask_equal (Map.find_exn previous name) (Map.find_exn next name))
          then next
          else fixed_point next
        in
        fixed_point initial
  in
  let required_upper_bounds =
    List.fold
      (DependencyGraph.topsort graph)
      ~init:(Map.empty (module QualIdent))
      ~f:solve_component
  in
  { declarations; by_name; required_upper_bounds }
