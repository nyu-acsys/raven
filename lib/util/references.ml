(** The names that a program uses and what they refer to, collected while type-checking it
    and printed for an editor by `--lsp-mode --lsp-annotations`: for hovers, and for going
    to a definition. *)

module Err = Error
open Base

type t = {
  use_loc : Loc.t;  (** The name as written. *)
  use_name : string;  (** The name as written, without qualification. *)
  target : string;  (** The qualified name of what it refers to. *)
  kind : string;
  def_loc : Loc.t;  (** Where that is declared. *)
  detail : string option Lazy.t;  (** Its declaration, for a hover. *)
}

(** The [references], latest first, that lie in [files] and span the name as written
    there, in the order of their locations, each with the index of what it refers to in
    the list of symbols, which is the second result. A reference elsewhere uses a name the
    verifier generated, such as an implicit argument. Of several at the same location, the
    latest is the type checker's final resolution. *)
let to_json ~(files : string list) (references : t list) : Yojson.Safe.t * Yojson.Safe.t =
  let contents = Hashtbl.create (module String) in
  let content file =
    Hashtbl.find_or_add contents file ~default:(fun () ->
        if Stdlib.Sys.file_exists file then Some (Stdio.In_channel.read_all file)
        else None)
  in
  let spans_name r =
    let file = Loc.file_name r.use_loc in
    List.mem files file ~equal:String.equal
    && Option.exists (content file) ~f:(fun content ->
        let pos = Loc.start_index r.use_loc and len = String.length r.use_name in
        Loc.end_index r.use_loc - pos = len
        && pos >= 0
        && pos + len <= String.length content
        && String.equal (String.sub content ~pos ~len) r.use_name)
  in
  let references =
    List.filter references ~f:spans_name
    |> List.stable_sort ~compare:(fun r1 r2 -> Loc.compare r1.use_loc r2.use_loc)
    |> List.remove_consecutive_duplicates ~which_to_keep:`First ~equal:(fun r1 r2 ->
        Loc.equal r1.use_loc r2.use_loc)
  in
  (* A symbol is identified by its name and declaration, which tell apart local variables
     of the same name. *)
  let indices = Hashtbl.create (module String) in
  let symbols = ref [] in
  let index r =
    let key = r.target ^ "@" ^ Loc.to_string_simple r.def_loc in
    Hashtbl.find_or_add indices key ~default:(fun () ->
        let detail =
          match Lazy.force r.detail with
          | Some detail -> [ ("detail", `String detail) ]
          | None -> []
        in
        symbols :=
          `Assoc
            ([ ("name", `String r.target); ("kind", `String r.kind) ]
            @ [ ("definition", `Assoc (Err.loc_to_lsp_fields r.def_loc)) ]
            @ detail)
          :: !symbols;
        Hashtbl.length indices)
  in
  (* A name is on one line, and its file is needed only with several. *)
  let file r =
    match files with [ _ ] -> [] | _ -> [ ("file", `String (Loc.file_name r.use_loc)) ]
  in
  let references =
    List.map references ~f:(fun r ->
        `Assoc
          (file r
          @ [
              ("line", `Int (Loc.start_line r.use_loc));
              ("start_col", `Int (Loc.start_col r.use_loc));
              ("end_col", `Int (Loc.end_col r.use_loc));
              ("symbol", `Int (index r));
            ]))
  in
  (`List references, `List (List.rev !symbols))
