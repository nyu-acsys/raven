open Base
open Ast
open Util
open NamespaceContract

type t = {
  namespaces : namespace_decl Map.M(QualIdent).t;
  equations : NamespaceEquations.t;
}

let canonical_name ?(rename = Fn.id) name =
  let open Rewriter.Syntax in
  let rec fixed seen name =
    let renamed = rename name in
    let* table = Rewriter.get_table in
    let resolved =
      match
        SymbolTbl.resolve_and_find ~implementation:true ~read_only:true renamed
          (SymbolTbl.goto renamed table)
      with
      | None -> renamed
      | Some (_, resolved, _, _) -> resolved
    in
    let next = rename resolved in
    if QualIdent.equal next name || Set.mem seen next then Rewriter.return next
    else fixed (Set.add seen name) next
  in
  fixed (Set.empty (module QualIdent)) name

let canonical_mask ?(rename = Fn.id) mask =
  let open Rewriter.Syntax in
  let+ mask =
    Rewriter.List.map mask ~f:(fun (head, args) ->
        let+ name = canonical_name ~rename (Callable.mask_head_name head) in
        (Callable.map_mask_head ~f:(fun _ -> name) head, args))
  in
  Callable.mask_canon mask

let align_body source target body =
  let renaming =
    List.zip source target |> function
    | Unequal_lengths ->
        Error.internal_error Loc.dummy "Namespace alias formal arities differ"
    | Ok pairs ->
        List.fold pairs
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map (source, target) ->
            Map.set map
              ~key:(QualIdent.from_ident source.Type.var_name)
              ~data:(Expr.from_var_decl target))
  in
  List.map body ~f:(fun (head, args) ->
      (head, List.map args ~f:(fun arg -> Expr.alpha_renaming arg renaming)))

let create ?(rename = Fn.id) ?(overrides = []) declarations =
  let open Rewriter.Syntax in
  let canonical declaration =
    Rewriter.in_scope_of declaration.name
      (let* name = canonical_name ~rename declaration.name in
       let+ definition =
         match declaration.definition with
         | Abstract -> Rewriter.return Abstract
         | Defined body ->
             let+ body = canonical_mask ~rename body in
             Defined body
       in
       { declaration with name; definition })
  in
  let source_declarations = declarations in
  let* declarations = Rewriter.List.map declarations ~f:canonical in
  let* overrides = Rewriter.List.map overrides ~f:canonical in
  let merge map declaration =
    Map.update map declaration.name ~f:(function
      | None -> declaration
      | Some previous ->
          let definition =
            match (previous.definition, declaration.definition) with
            | Abstract, definition -> definition
            | definition, Abstract -> definition
            | Defined left, Defined right ->
                Defined
                  (Callable.mask_union left
                     (align_body declaration.formals previous.formals right))
          in
          begin match previous.definition with
          | Abstract -> declaration
          | Defined _ -> { previous with definition }
          end)
  in
  let source_declarations =
    List.fold source_declarations ~init:(Map.empty (module QualIdent)) ~f:merge
  in
  let namespaces = List.fold declarations ~init:(Map.empty (module QualIdent)) ~f:merge in
  let heads declaration =
    match declaration.definition with
    | Abstract -> []
    | Defined body -> List.map body ~f:(fun (head, _) -> Callable.mask_head_name head)
  in
  let* table = Rewriter.get_table in
  let rec complete seen namespaces = function
    | [] -> Rewriter.return namespaces
    | name :: pending when Set.mem seen name -> complete seen namespaces pending
    | name :: pending ->
        let seen = Set.add seen name in
        let resolved =
          SymbolTbl.resolve_and_find ~implementation:true ~read_only:true name
            (SymbolTbl.goto name table)
        in
        let* copied =
          match resolved with
          | Some (original, _, _, subst) ->
              begin match Map.find source_declarations original with
              | Some ({ definition = Defined _; _ } as template) ->
                  let requalify = QualIdent.requalify (SymbolTbl.qid_subst subst) in
                  let* declaration =
                    NamespaceContract.map_state_namespace_decl
                      ~name:(fun name -> Rewriter.return (requalify name))
                      ~expr:(Rewriter.Expr.rewrite_qual_idents ~f:requalify)
                      ~typ:(Rewriter.Type.rewrite_qual_idents ~f:requalify)
                      template
                  in
                  let+ declaration = canonical { declaration with name } in
                  Some declaration
              | Some { definition = Abstract; _ } | None -> Rewriter.return None
              end
          | None -> Rewriter.return None
        in
        let namespaces, introduced =
          match copied with
          | None -> (namespaces, [])
          | Some declaration -> (merge namespaces declaration, heads declaration)
        in
        complete seen namespaces (introduced @ pending)
  in
  let pending =
    List.concat_map (Map.data namespaces) ~f:(fun declaration ->
        declaration.name :: heads declaration)
    @ List.concat_map overrides ~f:heads
  in
  let* namespaces = complete (Set.empty (module QualIdent)) namespaces pending in
  let namespaces =
    List.fold overrides ~init:namespaces ~f:(fun map declaration ->
        match declaration.definition with
        | Abstract -> map
        | Defined _ -> Map.set map ~key:declaration.name ~data:declaration)
  in
  Rewriter.return
    { namespaces; equations = NamespaceEquations.solve (Map.data namespaces) }

let normalize_mask ?(rename = Fn.id) state mask =
  NamespaceEquations.normalize_required ~resolve:(canonical_mask ~rename) state.equations
    mask

let covered ~by mask =
  List.for_all mask ~f:(fun entry ->
      List.exists by ~f:(fun bound ->
          match Callable.mask_entry_meet bound entry with
          | None -> false
          | Some meet -> Callable.compare_mask_entry meet entry = 0))

let rec prefixes name =
  name :: (if QualIdent.is_qualified name then prefixes (QualIdent.pop name) else [])

let concrete_origin table name =
  let owners =
    if QualIdent.is_qualified name then prefixes (QualIdent.pop name) else []
  in
  List.for_all owners ~f:(fun owner ->
      match Map.find table.SymbolTbl.tbl_symbols owner with
      | Some (Module.ModDef definition) ->
          (not definition.mod_decl.mod_decl_is_interface)
          && Option.is_none definition.mod_decl.mod_decl_sealed_target
      | _ -> true)

let ground table name =
  let rec check seen name =
    if Set.mem seen name then false
    else
      let seen = Set.add seen name in
      match
        SymbolTbl.resolve_and_find ~implementation:true ~read_only:true name
          (SymbolTbl.goto name table)
      with
      | None -> false
      | Some (original, _, _, subst) ->
          List.for_all (prefixes original) ~f:(fun owner ->
              match Map.find table.SymbolTbl.tbl_symbols owner with
              | Some (Module.ModDef definition) ->
                  (not definition.mod_decl.mod_decl_is_interface)
                  && Option.is_none definition.mod_decl.mod_decl_sealed_target
                  && ((not (Module.is_functor definition.mod_decl))
                     || SymbolTbl.module_is_instantiated owner definition.mod_decl subst)
                  && List.for_all (Module.formals definition.mod_decl) ~f:(fun formal ->
                      let parameter = QualIdent.append owner formal.mod_inst_name in
                      let actual =
                        QualIdent.requalify (SymbolTbl.qid_subst subst) parameter
                      in
                      (not (QualIdent.equal parameter actual)) && check seen actual)
              | _ -> true)
  in
  check (Set.empty (module QualIdent)) name

let rigid table left right =
  match (left, right) with
  | Callable.MaskHead.Invariant left, Callable.MaskHead.Invariant right ->
      if QualIdent.equal left right then false
      else
        begin match
          ( SymbolTbl.resolve_and_find ~implementation:true ~read_only:true left
              (SymbolTbl.goto left table),
            SymbolTbl.resolve_and_find ~implementation:true ~read_only:true right
              (SymbolTbl.goto right table) )
        with
        | Some (source_left, _, _, _), Some (source_right, _, _, _) ->
            concrete_origin table source_left
            && concrete_origin table source_right
            && ((not (QualIdent.equal source_left source_right))
               || (ground table left && ground table right))
        | _ -> false
        end
  | _ -> false

let rec entails ?(rename = Fn.id) state ~assumptions requirement =
  let open Rewriter.Syntax in
  let canonical requirement =
    let* left = canonical_mask ~rename requirement.left in
    let+ right = canonical_mask ~rename requirement.right in
    { requirement with left; right }
  in
  let* assumptions = Rewriter.List.map assumptions ~f:canonical in
  let* requirement = canonical requirement in
  let assumed left right =
    List.exists assumptions ~f:(fun assumption ->
        (covered ~by:assumption.left left && covered ~by:assumption.right right)
        || (covered ~by:assumption.right left && covered ~by:assumption.left right))
  in
  let* left = normalize_mask ~rename state requirement.left in
  let* right = normalize_mask ~rename state requirement.right in
  let same_invariant =
    List.exists left ~f:(fun (head, _) ->
        match head with
        | Callable.MaskHead.Dependencies _ -> false
        | Invariant _ ->
            List.exists right ~f:(fun (other, _) -> Callable.equal_mask_head head other))
  in
  if same_invariant then Rewriter.return false
  else
    let* table = Rewriter.get_table in
    let roots =
      Map.fold table.tbl_symbols
        ~init:(Set.empty (module QualIdent))
        ~f:(fun ~key:owner ~data roots ->
          match data with
          | Module.ModDef definition ->
              let roots =
                List.fold (Module.formals definition.mod_decl) ~init:roots
                  ~f:(fun roots formal ->
                    Set.add roots (QualIdent.append owner formal.Module.mod_inst_name))
              in
              List.fold definition.mod_def ~init:roots ~f:(fun roots -> function
                | Module.SymbolDef (ModInst { mod_inst_name; mod_inst_def = None; _ }) ->
                    Set.add roots (QualIdent.append owner mod_inst_name)
                | _ -> roots)
          | _ -> roots)
    in
    let* symbolic =
      Rewriter.List.map (left @ right) ~f:(fun ((head, _) as entry) ->
          let+ variable = mentions ~rename ~roots [ entry ] in
          (head, variable))
    in
    let variable head =
      List.exists symbolic ~f:(fun (other, variable) ->
          variable && Callable.equal_mask_head head other)
    in
    Rewriter.return
      (assumed requirement.left requirement.right
      || List.for_all left ~f:(fun ((head, _) as left) ->
          List.for_all right ~f:(fun ((other, _) as right) ->
              ((not (variable head || variable other)) && rigid table head other)
              || assumed [ left ] [ right ])))

and mentions ?(rename = Fn.id) ?(conservative = false) ~roots mask =
  let open Rewriter.Syntax in
  if Set.is_empty roots then Rewriter.return false
  else
    let* mask = canonical_mask ~rename mask in
    let+ table = Rewriter.get_table in
    let rec depends seen name =
      let name =
        if Module.is_unit_parameter_path name then QualIdent.pop name else name
      in
      if List.exists (prefixes name) ~f:(Set.mem roots) then true
      else if Set.mem seen name then conservative
      else
        let resolved =
          SymbolTbl.resolve_and_find ~implementation:true ~read_only:true name
            (SymbolTbl.goto name table)
        in
        let seen = Set.add seen name in
        List.exists (prefixes name) ~f:(fun owner ->
            match SymbolTbl.application_origin owner table with
            | Some (head, arguments) ->
                depends seen head
                || List.exists arguments ~f:(fun (_, actual) -> depends seen actual)
            | None -> false)
        ||
        match resolved with
        | None -> false
        | Some (_, _, _, subst) ->
            List.exists (SymbolTbl.qid_subst subst) ~f:(fun (source, actual) ->
                if Module.is_unit_parameter_path source then false
                else
                  match actual with
                  | [] -> false
                  | _ ->
                      let actual = QualIdent.from_list actual in
                      (not (Module.is_unit_parameter_path actual)) && depends seen actual)
    in
    List.exists mask ~f:(fun (head, _) ->
        depends (Set.empty (module QualIdent)) (Callable.mask_head_name head))
