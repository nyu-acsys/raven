(** What a run reports besides its result: the errors recorded at recovery points, the
    warnings, and for an editor the annotations, the status of members and the names the
    program uses. The driver creates one per run and every phase adds to it. It is
    mutable, so that a recovery point further out, which rolls back the state of the
    computation that failed, keeps what was recorded. *)

module Err = Error
open Base

(** Information about a program that an editor shows alongside its text, collected while
    checking it and printed by `--lsp-mode --lsp-annotations`. *)
module Annotations = struct
  type clause = { keyword : string; text : string; clause_loc : Loc.t }
  (** A clause of a contract: its keyword, its text as written, and its location. *)

  type member = { origin : string; text : string; member_loc : Loc.t }
  (** A member that a module inherits: the interface it originates from, its declaration
      as written there, and its location. *)

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
end

(** The verification status of the program's members, printed for an editor by `--lsp-mode
    --lsp-annotations`. A member's status is the worst outcome of the procedures checked
    for it: its own, and those that elaboration and lowering generate from its loops,
    contract and quantifiers, which lie within its text. A module summarizes the status of
    the members nested in it. *)
module MemberStatus = struct
  (** The outcome of checking a procedure, from best to worst. *)
  type outcome = Verified | Timeout | Failed [@@deriving compare]

  (** The status of a member, from best to worst. *)
  type status = Verified | Skipped | Timeout | Failed [@@deriving compare]

  type member = {
    name : string;  (** Qualified by the modules it is nested in. *)
    kind : string;
    name_loc : Loc.t;
    extent : Loc.t;  (** Its name, contract and body. *)
    checked : bool;
        (** Whether it is checked itself: a procedure or lemma with a body. *)
    inherited : bool;
        (** Whether a module inherits it, such as a lemma for an axiom of its interface.
        *)
  }

  type procedure = { proc_loc : Loc.t; proc_name : string; proc_kind : string }
  (** A checked procedure: where it is declared, its qualified name and its kind. *)

  type group = { group_name : string; group_kind : string; group_loc : Loc.t }
  (** A module or interface, which summarizes the members nested in it. *)

  let contains (outer : Loc.t) (inner : Loc.t) =
    String.equal (Loc.file_name outer) (Loc.file_name inner)
    && Loc.compare_position outer.loc_start inner.loc_start <= 0
    && Loc.compare_position inner.loc_end outer.loc_end <= 0

  let size (loc : Loc.t) = Loc.end_index loc - Loc.start_index loc

  (** The innermost of [members] whose text contains [loc]. *)
  let innermost (members : member list) (loc : Loc.t) =
    List.filter members ~f:(fun m -> contains m.extent loc)
    |> List.min_elt ~compare:(fun m1 m2 -> Int.compare (size m1.extent) (size m2.extent))

  let status_to_string = function
    | Verified -> "verified"
    | Skipped -> "skipped"
    | Timeout -> "timeout"
    | Failed -> "failed"

  let of_outcome : outcome -> status = function
    | Verified -> Verified
    | Timeout -> Timeout
    | Failed -> Failed

  (** The members that the [groups] inherit, from the [results] of the procedures declared
      at the name of a group rather than within one of the [members]. *)
  let inherited_statuses members groups (results : (procedure * outcome) list) =
    List.filter_map results ~f:(fun (proc, outcome) ->
        if Option.is_some (innermost members proc.proc_loc) then None
        else
          List.find groups ~f:(fun group -> Loc.equal group.group_loc proc.proc_loc)
          |> Option.map ~f:(fun group ->
              let base = List.last_exn (String.split proc.proc_name ~on:'.') in
              let member =
                {
                  name = group.group_name ^ "." ^ base;
                  kind = proc.proc_kind;
                  name_loc = group.group_loc;
                  extent = group.group_loc;
                  checked = true;
                  inherited = true;
                }
              in
              (member, outcome)))
    |> List.sort_and_group ~compare:(fun (m1, _) (m2, _) ->
        String.compare m1.name m2.name)
    |> List.map ~f:(fun same ->
        let worst =
          List.map same ~f:snd
          |> List.max_elt ~compare:compare_outcome
          |> Option.value_exn
        in
        (fst (List.hd_exn same), of_outcome worst))

  (** The status of each of [members], and of those that the [groups] inherit, given the
      [results] of the checked procedures. A checked member without a result of its own
      was skipped if the run was [aborted]. There are none if nothing was checked. *)
  let statuses ~aborted (members : member list) groups
      (results : (procedure * outcome) list) =
    if List.is_empty results then []
    else
      let attributed =
        List.filter_map results ~f:(fun (proc, outcome) ->
            Option.map (innermost members proc.proc_loc) ~f:(fun m ->
                (m, proc.proc_loc, outcome)))
      in
      let own_statuses =
        List.filter_map members ~f:(fun member ->
            let own = List.filter attributed ~f:(fun (m, _, _) -> phys_equal m member) in
            let worst =
              List.map own ~f:(fun (_, _, outcome) -> outcome)
              |> List.max_elt ~compare:compare_outcome
            in
            let checked_itself =
              List.exists own ~f:(fun (_, loc, _) -> Loc.equal loc member.name_loc)
            in
            match worst with
            | Some ((Failed | Timeout) as outcome) -> Some (member, of_outcome outcome)
            | _ when aborted && member.checked && not checked_itself ->
                Some (member, Skipped)
            | Some Verified -> Some (member, Verified)
            | None -> None)
      in
      own_statuses @ inherited_statuses members groups results

  (** The worst status of the members nested in [group], and how many have each status. *)
  let summary (statuses : (member * status) list) (group : group) =
    let nested =
      List.filter_map statuses ~f:(fun (member, status) ->
          Option.some_if
            (String.is_prefix member.name ~prefix:(group.group_name ^ "."))
            status)
    in
    Option.map (List.max_elt nested ~compare:compare_status) ~f:(fun worst ->
        let counts =
          List.sort_and_group nested ~compare:compare_status
          |> List.map ~f:(fun same ->
              (status_to_string (List.hd_exn same), `Int (List.length same)))
        in
        (worst, counts))

  let to_json ~aborted members groups results : Yojson.Safe.t =
    let statuses = statuses ~aborted members groups results in
    let entry loc name kind status extra =
      `Assoc
        (Err.loc_to_lsp_fields loc
        @ [
            ("name", `String name);
            ("kind", `String kind);
            ("status", `String (status_to_string status));
          ]
        @ extra)
    in
    `List
      (List.map statuses ~f:(fun (member, status) ->
           entry member.name_loc member.name member.kind status
             (if member.inherited then [ ("inherited", `Bool true) ] else []))
      @ List.filter_map groups ~f:(fun group ->
          Option.map (summary statuses group) ~f:(fun (status, counts) ->
              entry group.group_loc group.group_name group.group_kind status
                [ ("counts", `Assoc counts) ])))
end

(** The names that a program uses and what they refer to, collected while type-checking it
    and printed for an editor by `--lsp-mode --lsp-annotations`: for hovers, and for going
    to a definition. *)
module References = struct
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
      the list of symbols, which is the second result. A reference elsewhere uses a name
      the verifier generated, such as an implicit argument. Of several at the same
      location, the latest is the type checker's final resolution. *)
  let to_json ~(files : string list) (references : t list) : Yojson.Safe.t * Yojson.Safe.t
      =
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
      match files with
      | [ _ ] -> []
      | _ -> [ ("file", `String (Loc.file_name r.use_loc)) ]
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
end

(** {1 The accumulator} *)

type t = {
  mutable errors : Err.t list list;  (** Latest first. *)
  mutable aborted : bool;  (** Whether more than [max_errors] errors were found. *)
  max_errors : int option;
  collect_warnings : bool;
      (** Whether warnings are reported with the errors, for an editor, or logged. *)
  mutable warnings : Err.t list;  (** Latest first. *)
  mutable annotations : Annotations.t list;
  mutable members : MemberStatus.member list;  (** The program's, for their status. *)
  mutable groups : MemberStatus.group list;  (** The program's modules. *)
  reference_files : string list;  (** The files whose names are collected, if any. *)
  mutable references : References.t list;  (** The names the program uses. *)
  mutable results : (MemberStatus.procedure * MemberStatus.outcome) list;
      (** The outcomes of the checked procedures. *)
  origins : (string, string) Hashtbl.t;
      (** The interface each inherited member originates from, by the qualified name of
          the member in the module that inherits it. *)
}

let create ?max_errors ?(collect_warnings = false) ?(reference_files = []) () =
  {
    errors = [];
    aborted = false;
    max_errors;
    collect_warnings;
    warnings = [];
    annotations = [];
    members = [];
    groups = [];
    reference_files;
    references = [];
    results = [];
    origins = Hashtbl.create (module String);
  }

(** The number of errors recorded, counting each diagnostic once. *)
let error_count d = List.length d.errors

(** Records the diagnostic [diag], a primary error followed by its related locations, or
    sets [aborted] if it would exceed [max_errors]. An empty [diag] is a failure whose
    cause was already reported. *)
let record_error d (diag : Err.t list) =
  if not (List.is_empty diag || d.aborted) then begin
    let errors = diag :: d.errors in
    match d.max_errors with
    | Some limit when List.length (Err.merge_diagnostics errors) > limit ->
        d.aborted <- true
    | _ -> d.errors <- errors
  end

(** The recorded errors in source order, followed by a note if checking was aborted. *)
let report_errors d : Err.t list =
  let errors =
    List.rev d.errors |> Err.merge_diagnostics |> Err.sort_diagnostics |> List.concat
  in
  match d.max_errors with
  | Some limit when d.aborted ->
      errors
      @ [
          ( Err.Limit,
            Loc.dummy,
            Printf.sprintf "Stopped after %d errors; use --max-errors to change the limit"
              limit );
        ]
  | _ -> errors

let has_errors d = (not (List.is_empty d.errors)) || d.aborted

let warning d loc msg =
  if d.collect_warnings then d.warnings <- (Err.Warning, loc, msg) :: d.warnings
  else Logs.warn (fun m -> m "%s%s" (Loc.to_string loc) msg)

let warnings d = List.rev d.warnings

let record_annotation d (annotation : Annotations.t) =
  d.annotations <- annotation :: d.annotations

let set_origin d ~member origin = Hashtbl.set d.origins ~key:member ~data:origin
let origin d ~member ~default = Option.value (Hashtbl.find d.origins member) ~default
let annotations_to_json d = Annotations.all_to_json d.annotations

let set_members d (members, groups) =
  d.members <- members;
  d.groups <- groups

let record_result d proc outcome = d.results <- (proc, outcome) :: d.results

let members_to_json d =
  MemberStatus.to_json ~aborted:d.aborted d.members d.groups d.results

let record_reference d reference = d.references <- reference :: d.references

(** Whether the names used at [loc] are collected. *)
let collects_references d loc =
  List.mem d.reference_files (Loc.file_name loc) ~equal:String.equal

let references_to_json d = References.to_json ~files:d.reference_files d.references
