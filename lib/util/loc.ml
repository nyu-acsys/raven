(** Source code locations *)

module Opt = Option

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

(** [file_name loc], shortened to be relative to the current directory when it's
    underneath it -- for display only. Locations are always stored (and looked up,
    e.g. in [context] below) by the real, absolute path: that's what the LSP JSON
    output ([Error.to_lsp_json]) sends as-is for the editor to resolve against an open
    document's URI, and what the file-inclusion dedup logic in bin/raven.ml keys on.
    Neither of those should see a shortened path; only human-facing text (this
    module's [to_string] and [to_string_simple]) should. *)
let display_file_name loc =
  let fname = file_name loc in
  (* [fname] is always forward-slash-normalized (see normalizeFilename in
     bin/raven.ml), but Sys.getcwd () returns a native path -- backslash-separated on
     Windows -- so it has to be normalized the same way before comparing prefixes. *)
  let cwd =
    Stdlib.Sys.getcwd ()
    |> String.map ~f:(function '\\' -> '/' | c -> c)
    |> fun s -> s ^ "/"
  in
  if String.is_prefix fname ~prefix:cwd then
    String.drop_prefix fname (String.length cwd)
  else fname

let to_end loc = { loc with loc_start = loc.loc_end }
let to_start loc = { loc with loc_end = loc.loc_start }

(** The final character of [loc], for pointing at a closing delimiter itself
    rather than at the empty position just past it as [to_end] does. Degenerates
    to [to_end] when [loc] ends at the very start of a line, where there is no
    preceding character on that line to point at. *)
let last_char loc =
  let e = loc.loc_end in
  if e.pos_cnum <= e.pos_bol then to_end loc
  else { loc_start = { e with pos_cnum = e.pos_cnum - 1 }; loc_end = e }

let start_index loc = loc.loc_start.pos_cnum
let end_index loc = loc.loc_end.pos_cnum


let merge l1 l2 =
  assert (String.equal (file_name l1) (file_name l2));
  let spos =
    let c = compare_position l1.loc_start l2.loc_start in
    if c <= 0 then l1.loc_start else l2.loc_start
  in
  let epos =
    let c = compare_position l1.loc_end l2.loc_end in
    if c >= 0 then l1.loc_end else l2.loc_end
  in
  make spos epos

let to_string_simple loc =
  if start_line loc <> end_line loc then
    Printf.sprintf "%s:%d:%d" (display_file_name loc) (start_line loc) (start_col loc)
  else
    let start_col, end_col =
      if start_col loc = end_col loc then
        if start_col loc = 0 then (0, 1) else (start_col loc - 1, end_col loc)
      else (start_col loc, end_col loc)
    in
    Printf.sprintf "%s:%d:%d-%d" (display_file_name loc) (start_line loc) start_col
      end_col

(** Extension-supplied library sources (e.g. `well_founded_order.rav`), registered by
    the driver once the active extension is known. [Library.sources] only covers the
    core standard library, which is fixed at compile time; extension libraries vary
    with `--extension`, so they can't be baked in here the same way. Locations inside
    either are virtual: there is no real file on disk to fall back to reading. *)
let registered_sources : (string * string) list ref = ref []
let register_sources sources = registered_sources := sources

(** Every embedded library source: the fixed core standard library plus whatever the
    active extension registered. Each is named by its path relative to the repository
    root (see [Library.sources]). *)
let library_sources () = Library.sources @ !registered_sources

let library_source_content (name : string) : string option =
  List.find_map (library_sources ()) ~f:(fun (n, src) ->
      if String.equal n name then Some src else None)

(** Whether [name] denotes an embedded library source rather than a file on disk. *)
let is_library_source name = Opt.is_some (library_source_content name)

(* Ancestors of [dir], innermost first: "/a/b" -> ["/a/b"; "/a"; "/"] *)
let rec ancestors dir =
  let parent = Stdlib.Filename.dirname dir in
  if String.equal parent dir then [ dir ] else dir :: ancestors parent

(** Join with '/', flattening any '\' the platform contributed. Library sources are named
    by a '/'-separated path (see [Library.sources]), and Raven normalizes paths to '/'
    elsewhere too (see [normalizeFilename] in bin/raven.ml), so joining with
    [Filename.concat] would hand back a mix of both separators on Windows -- ugly in a
    diagnostic, and awkward for a client that has to escape it into JSON. Windows accepts
    '/' in paths, so the result is still openable there. *)
let join_path dir name =
  let to_slash = String.map ~f:(function '\\' -> '/' | c -> c) in
  let dir = to_slash dir in
  let dir = String.rstrip ~drop:(Char.equal '/') dir in
  dir ^ "/" ^ to_slash name

let library_real_path_cache : (string, string option) Hashtbl.t = Hashtbl.create (module String)

(** An on-disk file byte-identical to the embedded library source [name], if one can be
    found -- i.e. this binary is running inside a checkout it was built from. [name] is
    a repository-relative path, so a candidate root need only contain it.

    Roots come from the executable's own location and from the working directory, tried
    outermost first so that a source tree wins over dune's `_build` copy of it: both
    match byte-for-byte, but only the former is worth opening in an editor.

    Comparing content is what makes this safe. A checkout at a different revision, or a
    library file edited since the binary was built, simply fails to match and is
    rejected -- rather than being reported with line numbers that no longer line up
    with what was actually verified. *)
let library_real_path (name : string) : string option =
  match Hashtbl.find library_real_path_cache name with
  | Some cached -> cached
  | None ->
      let result =
        match library_source_content name with
        | None -> None
        | Some embedded ->
            let roots =
              ancestors (Stdlib.Filename.dirname Stdlib.Sys.executable_name)
              @ ancestors (Stdlib.Sys.getcwd ())
              |> List.dedup_and_sort ~compare:(fun a b ->
                     match Int.compare (String.length a) (String.length b) with
                     | 0 -> String.compare a b
                     | c -> c)
            in
            List.find_map roots ~f:(fun root ->
                let candidate = join_path root name in
                if Stdlib.Sys.file_exists candidate then
                  let content = Stdio.In_channel.read_all candidate in
                  if String.equal content embedded then Some candidate else None
                else None)
      in
      Hashtbl.set library_real_path_cache ~key:name ~data:result;
      result

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
    List.find_map (Library.sources @ !registered_sources) ~f:(fun (lib_file_name, lib_source) ->
        if String.(file_name loc = lib_file_name) then
          let lib_source_str = String.split_lines lib_source in
          let ctx = List.nth_exn lib_source_str (start_line loc - 1) in
          Some ctx
        else None)
    |> Opt.lazy_value ~default:(fun () ->
      let ic = Stdio.In_channel.create (file_name loc) in
      let ctx = in_channel_line ic (start_line loc - 1) in
      let _ = Stdio.In_channel.close ic in
      ctx)
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
    Printf.sprintf "File \"%s\", line %d, columns %d-%d:\n%s" (display_file_name loc)
      (start_line loc) (start_col loc) (end_col loc) (context loc)
  else
    Printf.sprintf "File \"%s\", line %d, column %d to line %d, column %d:\n%s"
      (display_file_name loc) (start_line loc) (start_col loc) (end_line loc)
      (end_col loc) (context loc)

let ( = ) = equal
