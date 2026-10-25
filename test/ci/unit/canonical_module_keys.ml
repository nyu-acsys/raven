open Base
open Raven
open Ast

let loc = Util.Loc.dummy
let id ?(number = 0) text = Ident.make loc text number
let qi ids = QualIdent.from_list ids
let nested = qi [ id "A"; id "B" ]
let dotted = qi [ id "A.B" ]
let flat = qi [ id "A_B" ]
let numbered = qi [ id ~number:1 "A"; id "B" ]
let different key left right = assert (not (String.equal (key left) (key right)))

let () =
  List.iter [ dotted; flat; numbered ] ~f:(different ProgUtils.structural_qid_key nested);
  let displayed = qi [ Ident.with_display ~text:"unrelated" (id "A"); id "B" ] in
  assert (
    String.equal
      (ProgUtils.structural_qid_key nested)
      (ProgUtils.structural_qid_key displayed));
  List.iter [ dotted; flat; numbered ] ~f:(fun other ->
      different ProgUtils.canonical_type_key (Type.var nested) (Type.var other));
  different ProgUtils.canonical_type_key Type.int (Type.var (qi [ id "Int" ]));
  List.iter [ dotted; flat; numbered ] ~f:(fun other ->
      different
        (fun interface_qual_ident ->
          ProgUtils.rep_module_name_string ~interface_qual_ident Type.int)
        nested other;
      different
        (ProgUtils.rep_module_name_string ~interface_qual_ident:(qi [ id "Interface" ]))
        (Type.var nested) (Type.var other);
      different
        (ProgUtils.field_module_name_string ~interface_qual_ident:(qi [ id "Interface" ]))
        nested other);
  let application head argument =
    ProgUtils.canonical_module_name ProgUtils.inst_mod_ident_prefix
      [ ProgUtils.structural_qid_key head; ProgUtils.structural_qid_key argument ]
  in
  different (fun head -> application head nested) nested dotted;
  different (application nested) nested dotted;
  different (ProgUtils.canonical_module_name "Prefix$$") [ "A$$B"; "C" ] [ "A"; "B$$C" ];
  different (ProgUtils.canonical_module_name "Prefix$$") [ "." ] [ "_2E" ]
