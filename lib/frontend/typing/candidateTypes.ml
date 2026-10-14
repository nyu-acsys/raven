open Base
open Ast

type error =
  | Unknown_type of QualIdent.t
  | Cyclic_alias of QualIdent.t
  | Needs_instantiation of QualIdent.t
  | Not_type of QualIdent.t

let rec rewrite_type ~f (Type.App (head, args, attr)) =
  let head =
    match head with
    | Type.Var qi -> Type.Var (f qi)
    | Type.AtomicToken qi -> Type.AtomicToken (f qi)
    | head -> head
  in
  Type.App (head, List.map args ~f:(rewrite_type ~f), attr)

(** Expands the type aliases in [tp], resolving names with the monadic [lookup]. *)
let normalize ~lookup tp =
  let open Rewriter.Syntax in
  let rec expand visiting (Type.App (head, args, _) as tp) =
    match (head, args) with
    | Type.Var qi, _ :: _ -> Rewriter.return (Error (Needs_instantiation qi))
    | Type.Var qi, [] ->
        let* found = lookup qi in
        begin match found with
        | None -> Rewriter.return (Error (Unknown_type qi))
        | Some (resolved, _) when Set.mem visiting resolved ->
            Rewriter.return (Error (Cyclic_alias resolved))
        | Some (resolved, symbol) ->
            let definition =
              Rewriter.Symbol.extract symbol ~f:(fun _ requalify -> function
                | Module.TypeDef { type_def_expr; _ } ->
                    Ok (Option.map type_def_expr ~f:(rewrite_type ~f:requalify))
                | Module.ModDef { mod_decl = { mod_decl_rep = Some rep; _ }; _ } ->
                    Ok (Some (Type.var (QualIdent.append resolved rep)))
                | _ -> Error (Not_type resolved))
            in
            begin match definition with
            | Error error -> Rewriter.return (Error error)
            | Ok (None | Some (Type.App (Data _, _, _))) ->
                Rewriter.return (Ok (Type.var resolved |> Type.set_ghost_to tp))
            | Ok (Some definition) ->
                let+ expanded = expand (Set.add visiting resolved) definition in
                Result.map expanded ~f:(fun expanded -> Type.set_ghost_to tp expanded)
            end
        end
    | _ ->
        let+ args = Rewriter.List.map args ~f:(expand visiting) in
        Result.map (Result.all args) ~f:(fun args ->
            Type.App (head, args, Type.attr_of tp))
  in
  expand (Set.empty (module QualIdent)) tp

(** Resolves [qi] without counting as a read of a local variable. *)
let lookup qi = Rewriter.resolve_and_find_opt ~read_only:true qi
