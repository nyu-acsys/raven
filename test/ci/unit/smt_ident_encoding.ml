open Base
open Raven
open Backend
open Ast

let id ?(num = 0) name = Ident.make Util.Loc.dummy name num
let encode qi = Stdlib.Format.asprintf "%a" Smt.SmtLibAst.pr_smt_ident qi

let () =
  let names =
    [
      "value";
      "value'";
      "value_";
      "value''";
      "value'_";
      "value_'";
      "value__";
      "_";
      "_0";
      "in";
      "!in";
      "union";
      "select";
      "::";
      "+|";
      "+\\";
      "$RavenEncoded$247c";
      "$RavenEncoded$";
    ]
  in
  let identifiers =
    List.concat_map names ~f:(fun name ->
        List.concat_map [ 0; 1; 2 ] ~f:(fun num ->
            List.map
              [ []; [ id "M" ]; [ id "M'" ]; [ id "M_" ] ]
              ~f:(fun path -> QualIdent.make path (id ~num name))))
  in
  let encoded = List.map identifiers ~f:encode in
  assert (Set.length (Set.of_list (module String) encoded) = List.length identifiers);
  (* A literal spelling of an escaped symbol must not alias the encoded identifier. *)
  List.iter [ "+|"; "+\\" ] ~f:(fun name ->
      let encoded = encode (QualIdent.from_ident (id name)) in
      assert (not (String.equal encoded (encode (QualIdent.from_ident (id encoded))))))
