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

let normalize ~lookup tp =
  let rec expand visiting (Type.App (head, args, _) as tp) =
    match (head, args) with
    | Type.Var qi, _ :: _ -> Error (Needs_instantiation qi)
    | Type.Var qi, [] ->
        begin match lookup qi with
        | None -> Error (Unknown_type qi)
        | Some (resolved, symbol) ->
            if Set.mem visiting resolved then Error (Cyclic_alias resolved)
            else
              let definition =
                Rewriter.Symbol.extract symbol ~f:(fun _ requalify -> function
                  | Module.TypeDef { type_def_expr; _ } ->
                      Ok (Option.map type_def_expr ~f:(rewrite_type ~f:requalify))
                  | Module.ModDef { mod_decl = { mod_decl_rep = Some rep; _ }; _ } ->
                      Ok (Some (Type.var (QualIdent.append resolved rep)))
                  | _ -> Error (Not_type resolved))
              in
              Result.bind definition ~f:(function
                | None | Some (Type.App (Data _, _, _)) ->
                    Ok (Type.var resolved |> Type.set_ghost_to tp)
                | Some definition ->
                    Result.map
                      (expand (Set.add visiting resolved) definition)
                      ~f:(fun expanded -> Type.set_ghost_to tp expanded))
        end
    | _ ->
        Result.map
          (List.map args ~f:(expand visiting) |> Result.all)
          ~f:(fun args -> Type.App (head, args, Type.attr_of tp))
  in
  expand (Set.empty (module QualIdent)) tp

let lookup tbl qi =
  match SymbolTbl.resolve_candidates ~read_only:true qi tbl with
  | Some [ (alias, target, subst) ] ->
      Option.map (Map.find tbl.SymbolTbl.tbl_symbols alias) ~f:(fun symbol ->
          (target, (alias, symbol, subst)))
  | _ -> None
