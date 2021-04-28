(** Source code locations *)

open Base
  
type position = Lexing.position

let compare_position p1 p2 =
  let open Lexing in
  let f1 = Stdlib.Obj.magic p1.pos_fname in
  let f2 = Stdlib.Obj.magic p2.pos_fname in
  let c1 = compare_int f1 f2 in
  if c1 <> 0 then c1 else
  compare_int p1.pos_cnum p2.pos_cnum

let equal_position p1 p2 =
  let open Lexing in
  phys_equal p1 p2 ||
  (String.equal p1.pos_fname p2.pos_fname &&
   Int.equal p1.pos_lnum p2.pos_lnum &&
   Int.equal p1.pos_cnum p2.pos_cnum)
    
type t =
    { loc_start: position; 

      loc_end: position;
    }
    [@@deriving compare, equal]

let mk_loc p1 p2 = { loc_start = p1; loc_end = p2 }
      
let dummy =
  { loc_start = Lexing.dummy_pos;
    loc_end = Lexing.dummy_pos;
  }
    
open Lexing
    
let column p = p.pos_cnum - p.pos_bol

let start_line loc = loc.loc_start.pos_lnum
let end_line loc = loc.loc_end.pos_lnum
let start_col loc = column loc.loc_start
let end_col loc = column loc.loc_start
let start_bol loc = loc.loc_start.pos_bol
let end_bol loc = loc.loc_end.pos_bol
let file_name loc = loc.loc_start.pos_fname


    
let merge l1 l2 =
  assert (String.equal (file_name l1) (file_name l2));
  let spos =
    let c = compare_position l1.loc_start l2.loc_start in
    if c >= 0 then l1.loc_start else l2.loc_start
  in
  let epos =
    let c = compare_position l1.loc_end l2.loc_end in
    if c >= 0 then l1.loc_end else l2.loc_end
  in
  mk_loc spos epos
    
let to_string loc =
  if loc.loc_start.pos_lnum = loc.loc_end.pos_lnum 
  then 
    Printf.sprintf "File \"%s\", line %d, columns %d-%d" 
      loc.loc_start.pos_fname loc.loc_start.pos_lnum (column loc.loc_start) (column loc.loc_end)
  else 
    Printf.sprintf "File \"%s\", line %d, column %d to line %d, column %d" 
      loc.loc_start.pos_fname loc.loc_start.pos_lnum (column loc.loc_start) loc.loc_end.pos_lnum (column loc.loc_end)

      
(*
let flycheck_string_of_src_pos pos =
  if pos.sp_start_line <> pos.sp_end_line 
  then Printf.sprintf "%s:%d:%d" pos.sp_file pos.sp_start_line pos.sp_start_col
  else 
    let start_col, end_col = 
      if pos.sp_start_col = pos.sp_end_col 
      then 
        if pos.sp_start_col = 0 
        then 0, 1
        else pos.sp_start_col - 1, pos.sp_end_col
      else pos.sp_start_col, pos.sp_end_col
    in
    Printf.sprintf "%s:%d:%d-%d" pos.sp_file pos.sp_start_line start_col end_col
*)

let (=) = equal
      
