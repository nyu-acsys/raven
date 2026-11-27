(** Immutable family ancestry and structural region coverage, over canonical, already
    type-checked declarations. *)

open Base
open Ast

type error = { name : QualIdent.t; loc : Util.Loc.t; message : string }

(* A region: a declaration and a prefix of its arguments, denoting the corresponding
   family. It must be constructed and consumed with the same hierarchy. *)
type atom = QualIdent.t * Expr.t list
type paths = int list Map.M(QualIdent).t Map.M(QualIdent).t

type t = {
  declarations : NamespaceContract.namespace_decl Map.M(QualIdent).t;
  paths : paths;
  aliases : QualIdent.t Map.M(QualIdent).t;
  declared_regions : QualIdentSet.t;
}

let failure ?loc name message =
  Error { name; loc = Option.value loc ~default:(QualIdent.to_loc name); message }

let projection_in paths ~descendant ~ancestor =
  Option.bind (Map.find paths descendant) ~f:(fun ancestors ->
      Map.find ancestors ancestor)

let prefix_equal shorter longer =
  List.length shorter <= List.length longer
  && List.equal Expr.alpha_equal shorter (List.take longer (List.length shorter))

let projected_prefix positions arguments =
  let rec project acc = function
    | [] -> List.rev acc
    | position :: rest ->
        begin match List.nth arguments position with
        | Some argument -> project (argument :: acc) rest
        | None -> List.rev acc
        end
  in
  project [] positions

let covers_in paths ~by:(ancestor, prefix) (descendant, args) =
  Option.exists (projection_in paths ~descendant ~ancestor) ~f:(fun positions ->
      prefix_equal prefix (projected_prefix positions args))

(** Validates a finite family forest. Parent keys must be projections of explicit child
    parameters. [Within] records known ancestry, not immediate parenthood. Names and
    referenced declarations must be present. Alias identities are resolved structurally.
    Unresolved declarations, missing targets, duplicate names, and cycles are rejected. *)
let create declarations =
  let open Util.Result.Syntax in
  let* declarations =
    List.fold_result declarations
      ~init:(Map.empty (module QualIdent))
      ~f:(fun known (declaration : NamespaceContract.namespace_decl) ->
        if Map.mem known declaration.name then
          failure declaration.name "Duplicate canonical namespace declaration"
        else Ok (Map.set known ~key:declaration.name ~data:declaration))
  in
  let rec canonical seen name =
    if Set.mem seen name then failure name "Cyclic namespace aliases"
    else
      match Map.find declarations name with
      | None ->
          failure name ("Unknown namespace alias target " ^ QualIdent.to_string_user name)
      | Some { alias = None; _ } -> Ok name
      | Some { alias = Some target; ancestry = Root; formals; _ } ->
          let* target = canonical (Set.add seen name) target in
          let target_decl = Map.find_exn declarations target in
          if List.length formals <> List.length target_decl.formals then
            failure name "Namespace alias has different arity"
          else Ok target
      | Some _ -> failure name "A namespace alias cannot declare ancestry"
  in
  let* aliases =
    List.fold_result (Map.keys declarations)
      ~init:(Map.empty (module QualIdent))
      ~f:(fun aliases name ->
        let+ target = canonical (Set.empty (module QualIdent)) name in
        Map.set aliases ~key:name ~data:target)
  in
  let declarations =
    Map.filter declarations ~f:(fun declaration -> Option.is_none declaration.alias)
  in
  let parent_projection (child : NamespaceContract.namespace_decl)
      (parent : Callable.ancestry_clause) =
    match
      Option.bind (Map.find aliases parent.ancestry_target) ~f:(Map.find declarations)
    with
    | None -> failure ~loc:parent.ancestry_loc child.name "Unknown namespace ancestor"
    | Some target ->
        if List.length parent.ancestry_args <> List.length target.formals then
          failure ~loc:parent.ancestry_loc child.name
            "Namespace ancestor has different arity"
        else
          Result.all
            (List.map parent.ancestry_args ~f:(function
              | Expr.App (Var variable, [], _) when not (QualIdent.is_qualified variable)
                ->
                  begin match
                    List.findi child.formals ~f:(fun _ formal ->
                        Ident.equal formal.Type.var_name (QualIdent.unqualify variable))
                  with
                  | Some (position, formal) when not formal.Type.var_implicit ->
                      Ok position
                  | Some _ | None ->
                      failure ~loc:parent.ancestry_loc child.name
                        "Namespace ancestor must project explicit identity parameters"
                  end
              | _ ->
                  failure ~loc:parent.ancestry_loc child.name
                    "Namespace ancestor must project explicit identity parameters"))
  in
  let* parents =
    List.fold_result (Map.data declarations)
      ~init:(Map.empty (module QualIdent))
      ~f:(fun parents child ->
        match child.NamespaceContract.ancestry with
        | Unresolved -> failure child.name "Unresolved namespace ancestry"
        | Root -> Ok parents
        | Declared parent ->
            let+ positions = parent_projection child parent in
            Map.set parents ~key:child.name
              ~data:(Map.find_exn aliases parent.ancestry_target, positions))
  in
  let rec visit visiting paths name =
    if Map.mem paths name then Ok paths
    else if Set.mem visiting name then failure name "Cyclic namespace ancestry"
    else
      let declaration = Map.find_exn declarations name in
      let self = List.init (List.length declaration.formals) ~f:Fn.id in
      let* ancestors, paths =
        match Map.find parents name with
        | None -> Ok (Map.empty (module QualIdent), paths)
        | Some (parent, positions) ->
            let* paths = visit (Set.add visiting name) paths parent in
            let+ ancestors =
              List.fold_result
                (Map.to_alist (Map.find_exn paths parent))
                ~init:(Map.empty (module QualIdent))
                ~f:(fun ancestors (ancestor, projection) ->
                  match Option.all (List.map projection ~f:(List.nth positions)) with
                  | None -> failure name "Invalid composed namespace projection"
                  | Some projection ->
                      Ok (Map.set ancestors ~key:ancestor ~data:projection))
            in
            (ancestors, paths)
      in
      Ok (Map.set paths ~key:name ~data:(Map.set ancestors ~key:name ~data:self))
  in
  let+ paths =
    List.fold_result (Map.keys declarations)
      ~init:(Map.empty (module QualIdent))
      ~f:(visit (Set.empty (module QualIdent)))
  in
  let declared_regions =
    Map.fold parents
      ~init:(Set.empty (module QualIdent))
      ~f:(fun ~key:child ~data:(parent, _) names -> Set.add (Set.add names child) parent)
  in
  { declarations; paths; aliases; declared_regions }

let canonical_name hierarchy name = Map.find hierarchy.aliases name

(** Positions in the descendant's arguments that give the ancestor's arguments. *)
let projection hierarchy ~descendant ~ancestor =
  Option.bind (canonical_name hierarchy descendant) ~f:(fun descendant ->
      Option.bind (canonical_name hierarchy ancestor) ~f:(fun ancestor ->
          projection_in hierarchy.paths ~descendant ~ancestor))

let declaration hierarchy name =
  Option.bind (canonical_name hierarchy name) ~f:(Map.find hierarchy.declarations)

(** Whether this declaration belongs to a component with a declared ancestry edge. *)
let is_declared_regional hierarchy name =
  Option.exists (canonical_name hierarchy name) ~f:(Set.mem hierarchy.declared_regions)

let has_regions hierarchy = not (Map.is_empty hierarchy.declarations)

(** Known ancestor argument prefix, stopping at the first unavailable projection. *)
let project_arguments hierarchy ~descendant ~ancestor arguments =
  Option.map (projection hierarchy ~descendant ~ancestor) ~f:(fun positions ->
      projected_prefix positions arguments)

(** A region may supply an argument prefix, denoting the corresponding family. *)
let region hierarchy name arguments =
  match declaration hierarchy name with
  | None -> failure name "Unknown namespace declaration"
  | Some declaration ->
      let expected = List.length declaration.formals in
      let actual = List.length arguments in
      if actual > expected then failure name "Namespace budget has different arity"
      else
        let name = declaration.name in
        Ok (name, arguments)

(** Sufficient structural coverage, independent of logical assumptions. *)
let covers hierarchy = covers_in hierarchy.paths

(** The region of a mask entry, if it names an invariant. *)
let mask_region hierarchy (head, arguments) =
  match head with
  | Callable.MaskHead.Invariant name -> Result.ok (region hierarchy name arguments)
  | Dependencies _ -> None

(** Whether a region of the mask entries [by] structurally covers that of [entry]. *)
let covers_entry hierarchy ~by entry =
  Option.exists (mask_region hierarchy entry) ~f:(fun target ->
      List.exists by ~f:(fun candidate ->
          Option.exists (mask_region hierarchy candidate) ~f:(fun by ->
              covers hierarchy ~by target)))
