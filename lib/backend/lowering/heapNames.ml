(** Names shared by heap translation and resource witness computation. *)

open Ast
open Util

let field_heap_name (field_name : qual_ident) =
  let field_name_str = QualIdent.to_string field_name in
  let field_name_str = ProgUtils.serialize field_name_str in
  Ident.make Loc.dummy (field_name_str ^ "$Heap") 0

let field_heap_name2 (field_name : qual_ident) =
  let field_name_str = QualIdent.to_string field_name in
  let field_name_str = ProgUtils.serialize field_name_str in
  Ident.make Loc.dummy (field_name_str ^ "$Heap2") 0

let pred_heap_name (pred_name : qual_ident) =
  let pred_name_str = QualIdent.to_string pred_name in
  let pred_name_str = ProgUtils.serialize pred_name_str in
  Ident.make Loc.dummy (pred_name_str ^ "$Heap") 0

let pred_heap_name2 (pred_name : qual_ident) =
  let pred_name_str = QualIdent.to_string pred_name in
  let pred_name_str = ProgUtils.serialize pred_name_str in
  Ident.make Loc.dummy (pred_name_str ^ "$Heap2") 0

let au_heap_name (callable_name : qual_ident) =
  let callable_name_str = QualIdent.to_string callable_name in
  let callable_name_str = ProgUtils.serialize callable_name_str in
  Ident.make Loc.dummy (callable_name_str ^ "$AU_Heap") 0

let au_heap_name2 (callable_name : qual_ident) =
  let callable_name_str = QualIdent.to_string callable_name in
  let callable_name_str = ProgUtils.serialize callable_name_str in
  Ident.make Loc.dummy (callable_name_str ^ "$AU_Heap2") 0
