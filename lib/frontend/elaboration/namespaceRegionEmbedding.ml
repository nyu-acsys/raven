(** Compare the visible projections of two separately checked forests. *)

open Base
open Ast

type family = { visible : QualIdent.t; expected : QualIdent.t; actual : QualIdent.t }

let failure name message =
  Error { NamespaceRegions.name; loc = QualIdent.to_loc name; message }

let show = QualIdent.to_string_user

let resolve hierarchy name =
  Option.bind (NamespaceRegions.canonical_name hierarchy name) ~f:(fun name ->
      Option.map (NamespaceRegions.declaration hierarchy name) ~f:(fun declaration ->
          (name, List.length declaration.NamespaceContract.formals)))

let family ~expected ~actual mapping visible =
  match (resolve expected visible, Map.find mapping visible) with
  | None, _ -> failure visible ("Unknown visible invariant " ^ show visible)
  | Some _, None -> failure visible ("Missing realization for invariant " ^ show visible)
  | Some (expected_name, expected_arity), Some supplied ->
      begin match resolve actual supplied with
      | None -> failure visible ("Unknown implementation invariant " ^ show supplied)
      | Some (_, actual_arity) when expected_arity <> actual_arity ->
          failure visible
            (Printf.sprintf "Implementation invariant %s has different identity arity"
               (show supplied))
      | Some (actual_name, _) ->
          let expected_decl =
            Option.value_exn (NamespaceRegions.declaration expected expected_name)
          in
          let actual_decl =
            Option.value_exn (NamespaceRegions.declaration actual actual_name)
          in
          begin match (expected_decl.ancestry, actual_decl.ancestry) with
          | Root, Declared _ ->
              failure visible
                ("Realization gives invariant root " ^ show visible
               ^ " an undeclared ancestor")
          | _ -> Ok { visible; expected = expected_name; actual = actual_name }
          end
      end

let check_ancestry ~expected ~actual ~descendant ~ancestor =
  let expected_path =
    NamespaceRegions.projection expected ~descendant:descendant.expected
      ~ancestor:ancestor.expected
  in
  let actual_path =
    NamespaceRegions.projection actual ~descendant:descendant.actual
      ~ancestor:ancestor.actual
  in
  let mismatch reason =
    failure descendant.visible
      (Printf.sprintf "Realization %s from %s to %s" reason (show descendant.visible)
         (show ancestor.visible))
  in
  match (expected_path, actual_path) with
  | None, None -> Ok ()
  | Some expected, Some actual when List.equal Int.equal expected actual -> Ok ()
  | Some _, None -> mismatch "does not preserve ancestry"
  | None, Some _ -> mismatch "introduces undeclared ancestry"
  | Some _, Some _ -> mismatch "changes the ancestry key projection"

let check_pair ~expected ~actual left right =
  match
    ( QualIdent.equal left.expected right.expected,
      QualIdent.equal left.actual right.actual )
  with
  | true, false ->
      failure left.visible
        (Printf.sprintf
           "Realization does not preserve the invariant alias between %s and %s"
           (show left.visible) (show right.visible))
  | false, true ->
      failure left.visible
        (Printf.sprintf "Realization identifies distinct invariants %s and %s"
           (show left.visible) (show right.visible))
  | true, true -> Ok ()
  | false, false ->
      let open Util.Result.Syntax in
      let* () = check_ancestry ~expected ~actual ~descendant:left ~ancestor:right in
      check_ancestry ~expected ~actual ~descendant:right ~ancestor:left

let check ~expected ~actual ~visible ~mapping =
  let open Util.Result.Syntax in
  let* mapping =
    match Map.of_alist (module QualIdent) mapping with
    | `Ok mapping -> Ok mapping
    | `Duplicate_key name ->
        failure name ("Multiple realizations for invariant " ^ show name)
  in
  let* families = Result.all (List.map visible ~f:(family ~expected ~actual mapping)) in
  let rec check_pairs = function
    | [] -> Ok ()
    | first :: rest ->
        let* () =
          List.fold_result rest ~init:() ~f:(fun () family ->
              check_pair ~expected ~actual first family)
        in
        check_pairs rest
  in
  check_pairs families
