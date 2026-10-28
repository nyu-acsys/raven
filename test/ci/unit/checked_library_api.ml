module A = Raven_api.Ast

let find_module parent name =
  List.find_map
    (function
      | A.Module.SymbolDef (A.Module.ModDef child)
        when String.equal (A.Ident.name child.mod_decl.mod_decl_name) name ->
          Some child
      | _ -> None)
    parent.A.Module.mod_def

let find parent name =
  match find_module parent name with
  | Some child -> child
  | None -> failwith ("Missing library module " ^ name)

let () =
  let library =
    match Raven_api.Library.standard_library () with
    | Ok library -> library
    | Error diagnostics ->
        failwith
          (String.concat "\n" (List.map Raven_api.Diagnostic.to_string diagnostics))
  in
  assert (String.equal (A.Ident.name library.mod_decl.mod_decl_name) "Library");
  let ra = find library "ResourceAlgebra" in
  assert ra.mod_decl.mod_decl_is_interface;
  let set_ra = find library "SetRA" in
  assert (not set_ra.mod_decl.mod_decl_is_interface);
  assert (
    List.exists
      (function
        | A.Module.SymbolDef (A.Module.TypeDef typ) ->
            String.equal (A.Ident.name typ.type_def_name) "T" && typ.type_def_rep
        | _ -> false)
      set_ra.mod_def)
