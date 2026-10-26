(** Public functor schemas derived from established nominal conformance. *)

open Base
open Ast
open Util
open TypingMonad

let rec public_members formals instructions =
  List.filter_map instructions ~f:(function
    | Module.Import _ | SymbolDef (ConstrDef _ | DestrDef _) -> None
    | SymbolDef (ModInst instance)
      when List.exists formals ~f:(fun formal ->
               Ident.equal instance.mod_inst_name formal.Module.mod_inst_name) ->
        None
    | SymbolDef (ModDef definition) ->
        Some
          (Module.SymbolDef
             (ModDef { definition with mod_def = public_members [] definition.mod_def }))
    | instruction -> Some instruction)

let make ~loc ~name ~interface ~target ~target_symbol ~definition =
  let open Rewriter.Syntax in
  let* interface, interface_symbol = Rewriter.resolve_and_find interface in
  begin match Rewriter.Symbol.orig_symbol interface_symbol with
  | Module.ModDef { mod_decl = { mod_decl_is_interface = true; _ }; _ } -> ()
  | _ -> Error.type_error loc "A sealed functor alias must name an interface"
  end;
  if not (Set.mem (Interfaces.implemented_interfaces target_symbol) interface) then
    TypingErrors.does_not_implement_error loc "Module" target interface;
  let interface_origin = Rewriter.Symbol.orig_qid interface_symbol in
  let* actuals =
    Interfaces.functor_interface_arguments ~loc ~interface:interface_origin target_symbol
  in
  let interface_formals = Interfaces.declared_parameters interface_symbol in
  let* scope = Rewriter.current_scope_id in
  let owner = QualIdent.append scope name in
  let* projected =
    match List.zip interface_formals actuals with
    | Unequal_lengths ->
        Error.type_error loc "The functor result has incompatible interface arguments"
    | Ok pairs ->
        let projected =
          List.fold pairs ~init:interface_symbol ~f:(fun symbol (formal, actual) ->
              Rewriter.Symbol.extend_subst
                ( QualIdent.append interface_origin formal.Module.mod_inst_name,
                  QualIdent.to_list actual )
                symbol)
          |> Rewriter.Symbol.extend_subst (interface_origin, QualIdent.to_list owner)
          |> Rewriter.Symbol.extend_subst (interface, QualIdent.to_list owner)
          |> Rewriter.Symbol.extend_subst (target, QualIdent.to_list owner)
        in
        Rewriter.Symbol.reify projected
  in
  let projected =
    match projected with
    | Module.ModDef definition -> definition
    | _ -> Error.type_error loc "Expected an interface definition"
  in
  let requalify qi =
    QualIdent.requalify (Rewriter.Symbol.subst target_symbol) qi
    |> QualIdent.requalify [ (target, QualIdent.to_list owner) ]
  in
  let* domain =
    Rewriter.List.map (Module.formals definition.Module.mod_decl) ~f:(fun formal ->
        let+ mapped =
          lift
            (Rewriter.Module.rewrite_qual_idents_in_symbol ~f:requalify
               (Module.ModInst formal))
        in
        match mapped with
        | Module.ModInst formal -> formal
        | _ -> Error.internal_error loc "Expected a functor parameter")
  in
  let parameters = (Module.with_formals definition.mod_decl domain).mod_decl_parameters in
  let returns =
    [
      ( interface_origin,
        List.map actuals ~f:(fun actual -> Module.ModArg (requalify actual)) );
    ]
  in
  let schema =
    Module.set_machine_free
      Module.
        {
          mod_decl =
            {
              empty_decl with
              mod_decl_name = name;
              mod_decl_parameters = parameters;
              mod_decl_returns = returns;
              mod_decl_is_sealed = true;
              mod_decl_interfaces =
                Set.inter
                  (Interfaces.implemented_interfaces target_symbol)
                  (Set.add (Interfaces.implemented_interfaces interface_symbol) interface);
              mod_decl_loc = loc;
            };
          mod_def = public_members interface_formals projected.mod_def;
        }
  in
  Rewriter.return schema

let introduce ~loc ~check_schema schema =
  lift (Rewriter.introduce_typecheck_symbol ~loc ~f:check_schema (Module.ModDef schema))
