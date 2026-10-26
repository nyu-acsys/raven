(** Generative result identities cannot escape into an applicative functor. *)

open Base
open Ast
open Util

let inside_named_functor table =
  let rec nearest = function
    | [] -> false
    | scope :: rest ->
        begin match Map.find table.SymbolTbl.tbl_symbols scope.SymbolTbl.scope_id with
        | Some
            (Module.ModDef { mod_decl = { mod_decl_parameters = UnitParameter; _ }; _ })
          ->
            false
        | Some
            (Module.ModDef
               { mod_decl = { mod_decl_parameters = NamedParameters _; _ }; _ }) ->
            true
        | _ -> nearest rest
        end
  in
  nearest (table.tbl_curr :: table.tbl_path)

let result_identity root =
  let open Rewriter.Syntax in
  let local name =
    List.is_prefix (QualIdent.to_list name) ~prefix:(QualIdent.to_list root)
      ~equal:Ident.equal
  in
  let reason name kind = Rewriter.return (Some (name, kind)) in
  let rec module_identity seen ~force name =
    let* resolved = Rewriter.resolve_and_find_opt name in
    match resolved with
    | None -> reason name "unresolved module identity"
    | Some (name, _) when (not force) && not (local name) -> Rewriter.return None
    | Some (name, symbol) ->
        (* Recursive signatures can revisit one declaration under growing paths. *)
        let source = Rewriter.Symbol.orig_qid symbol in
        if Set.mem seen name || Set.mem seen source then
          reason name "recursive module identity"
        else
          let* symbol = Rewriter.Symbol.reify symbol in
          begin match symbol with
          | Module.ModDef module_ ->
              members (Set.add (Set.add seen name) source) name module_.mod_def
          | _ -> reason name "unknown module result"
          end
  and members seen owner instructions =
    Rewriter.List.fold_left instructions ~init:None ~f:(fun found instruction ->
        match found with
        | Some _ -> Rewriter.return found
        | None ->
            begin match instruction with
            | Module.Import _ -> Rewriter.return None
            | Module.SymbolDef symbol ->
                let name = QualIdent.append owner (Symbol.to_name symbol) in
                begin match symbol with
                | Module.TypeDef { type_def_expr = None; _ } ->
                    reason name "abstract type"
                | TypeDef { type_def_expr = Some (Type.App (Data _, _, _)); _ } ->
                    reason name "data type"
                | FieldDef { field_alias = None; _ } -> reason name "field"
                | CallDef { call_decl = { call_decl_alias = Some _; _ }; _ } ->
                    Rewriter.return None
                | VarDef { var_init = None; _ } -> reason name "unspecified value"
                | CallDef
                    {
                      call_decl = { call_decl_kind = Func; _ };
                      call_def = FuncDef { func_body = None };
                    } ->
                    reason name "uninterpreted function"
                | CallDef call ->
                    begin match call.call_decl.call_decl_kind with
                    | Pred -> reason name "predicate"
                    | Invariant -> reason name "invariant"
                    | Proc when Callable.is_atomic call.call_decl ->
                        reason name "atomic update procedure"
                    | Func | Lemma | Proc -> Rewriter.return None
                    end
                | ModDef module_ -> members (Set.add seen name) name module_.mod_def
                | ModInst instance ->
                    module_identity seen
                      ~force:
                        (instance.mod_inst_is_sealed
                        ||
                        match instance.mod_inst_def with
                        | None | Some (ApplyUnit _) -> true
                        | Some (Alias _ | Apply _ | CanonicalApply _) -> false)
                      name
                | TypeDef _ | FieldDef _ | VarDef _ | ConstrDef _ | DestrDef _ ->
                    Rewriter.return None
                end
            end)
  in
  module_identity (Set.empty (module QualIdent)) ~force:true root

let check_application_context ~loc result =
  let open Rewriter.Syntax in
  let* table = Rewriter.get_table in
  if not (inside_named_functor table) then Rewriter.return ()
  else
    let+ identity = result_identity result in
    match identity with
    | None -> ()
    | Some (name, kind) ->
        Error.type_error loc
          (Printf.sprintf
             "A unit factory cannot be applied inside a named-parameter functor when its \
              result introduces a fresh %s (%s)"
             kind
             (QualIdent.to_string_user name))
