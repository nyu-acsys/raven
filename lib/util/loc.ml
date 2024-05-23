(** Source code locations *)

open Base

type position = Lexing.position = {
  pos_fname : string;
  pos_lnum : int;
  pos_bol : int;
  pos_cnum : int;
}
[@@deriving sexp]

let compare_position p1 p2 =
  let open Lexing in
  let f1 = Stdlib.Obj.magic p1.pos_fname in
  let f2 = Stdlib.Obj.magic p2.pos_fname in
  let c1 = compare_int f1 f2 in
  if c1 <> 0 then c1 else compare_int p1.pos_cnum p2.pos_cnum

let equal_position p1 p2 =
  let open Lexing in
  phys_equal p1 p2
  || String.equal p1.pos_fname p2.pos_fname
     && Int.equal p1.pos_lnum p2.pos_lnum
     && Int.equal p1.pos_cnum p2.pos_cnum

type t = { loc_start : position; loc_end : position }
[@@deriving compare, equal, sexp]

let make p1 p2 = { loc_start = p1; loc_end = p2 }
let dummy = { loc_start = Lexing.dummy_pos; loc_end = Lexing.dummy_pos }

open Lexing

let column p = p.pos_cnum - p.pos_bol
let start_line loc = loc.loc_start.pos_lnum
let end_line loc = loc.loc_end.pos_lnum
let start_col loc = column loc.loc_start
let end_col loc = column loc.loc_end
let start_bol loc = loc.loc_start.pos_bol
let end_bol loc = loc.loc_end.pos_bol
let file_name loc = loc.loc_start.pos_fname
let to_end loc = { loc with loc_start = loc.loc_end }
let to_start loc = { loc with loc_end = loc.loc_start }

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
  make spos epos

let to_string_simple loc =
  if start_line loc <> end_line loc then
    Printf.sprintf "%s:%d:%d" (file_name loc) (start_line loc) (start_col loc)
  else
    let start_col, end_col =
      if start_col loc = end_col loc then
        if start_col loc = 0 then (0, 1) else (start_col loc - 1, end_col loc)
      else (start_col loc, end_col loc)
    in
    Printf.sprintf "%s:%d:%d-%d" (file_name loc) (start_line loc) start_col
      end_col

let context loc =
  let rec in_channel_line ic (line_num : int) =
    let next_line =
      match Stdio.In_channel.input_line ic with
      | None -> Printf.sprintf "Cannot find line %s" (to_string_simple loc)
      | Some s -> s
    in

    if line_num = 0 then next_line
    else (
      assert (line_num > 0);
      in_channel_line ic (line_num - 1))
  in
  let ctx =
    if String.(file_name loc = "resource_algebra.rav") then
      let resource_algebra_str =
        String.split_lines Resource_algebra.resource_algebra
      in
      let ctx = List.nth_exn resource_algebra_str (start_line loc - 1) in
      ctx
    else
      let ic = Stdio.In_channel.create (file_name loc) in
      let ctx = in_channel_line ic (start_line loc - 1) in
      let _ = Stdio.In_channel.close ic in
      ctx
  in

  let highlight_prefix_len =
    1 + String.length (Int.to_string @@ start_line loc) + 2 + start_col loc
  in
  let highlight_suffix_len =
    max 1
    @@ (if start_line loc = end_line loc then end_col loc else String.length ctx)
       - start_col loc
  in
  Printf.sprintf "%d | %s\n%s%s\n" (start_line loc) ctx
    (String.make highlight_prefix_len ' ')
    (String.make highlight_suffix_len '^')

let to_string loc =
  if loc.loc_start.pos_lnum = loc.loc_end.pos_lnum then
    Printf.sprintf "File \"%s\", line %d, columns %d-%d:\n%s" (file_name loc)
      (start_line loc) (start_col loc) (end_col loc) (context loc)
  else
    Printf.sprintf "File \"%s\", line %d, column %d to line %d, column %d:\n%s"
      (file_name loc) (start_line loc) (start_col loc) (end_line loc)
      (end_col loc) (context loc)

let ( = ) = equal
