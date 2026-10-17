(** Information about a program that an editor shows alongside its text, collected while
    checking it and printed by `--lsp-mode --lsp-annotations`. *)

module Err = Error
open Base

type clause = { keyword : string; text : string; clause_loc : Loc.t }
(** A clause of a contract: its keyword, its text as written, and its location. *)

type member = { origin : string; text : string; member_loc : Loc.t }
(** A member that a module inherits: the interface it originates from, its declaration as
    written there, and its location. *)

type t =
  | InheritedMembers of {
      module_loc : Loc.t;  (** the name of the module or interface *)
      members : member list;
    }
  | InheritedContract of {
      member_loc : Loc.t;  (** the name of the member that inherits the contract *)
      source : string;  (** the interface member it inherits it from *)
      source_loc : Loc.t;
      clauses : clause list;
    }

let to_json (annotation : t) : Yojson.Safe.t =
  match annotation with
  | InheritedMembers { module_loc; members } ->
      `Assoc
        (Err.loc_to_lsp_fields module_loc
        @ [
            ("kind", `String "InheritedMembers");
            ( "members",
              `List
                (List.map members ~f:(fun { origin; text; member_loc } ->
                     `Assoc
                       ([ ("origin", `String origin); ("text", `String text) ]
                       @ Err.loc_to_lsp_fields member_loc))) );
          ])
  | InheritedContract { member_loc; source; source_loc; clauses } ->
      `Assoc
        (Err.loc_to_lsp_fields member_loc
        @ [
            ("kind", `String "InheritedContract");
            ("source", `String source);
            ("source_loc", `Assoc (Err.loc_to_lsp_fields source_loc));
            ( "clauses",
              `List
                (List.map clauses ~f:(fun { keyword; text; clause_loc } ->
                     `Assoc
                       ([ ("keyword", `String keyword); ("text", `String text) ]
                       @ Err.loc_to_lsp_fields clause_loc))) );
          ])

(** The [annotations] of the program's own members, not those of the library, each once,
    in the order of their locations. *)
let all_to_json (annotations : t list) : Yojson.Safe.t =
  let key = function
    | InheritedContract { member_loc; _ } -> member_loc
    | InheritedMembers { module_loc; _ } -> module_loc
  in
  `List
    (List.dedup_and_sort annotations ~compare:(fun a b -> Loc.compare (key a) (key b))
    |> List.filter ~f:(fun a -> not (Loc.is_library_source (Loc.file_name (key a))))
    |> List.map ~f:to_json)
