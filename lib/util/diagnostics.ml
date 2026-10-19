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
  (** The outcome of checking a procedure, from best to worst: [Cached] if it was verified
      before, as the cache of fingerprints shows, and [Pending] if it is still to be
      checked. *)
  type outcome = Cached | Verified | Pending | Timeout | Failed [@@deriving compare]

  (** The status of a member, from best to worst. *)
  type status = Verified | Pending | Skipped | Timeout | Failed [@@deriving compare]

  type member = {
    name : string;  (** Qualified by the modules it is nested in. *)
    kind : string;
    name_loc : Loc.t;
    extent : Loc.t;  (** Its name, contract and body. *)
    checked : bool;
        (** Whether it is known to be checked: a procedure or lemma with a body, or a
            function with a body and a postcondition. *)
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

  (** Whether checked procedures can be attributed to [member]: not to a field, type,
      constant or module instance, which are listed only for an outline. *)
  let attributable member =
    not (List.mem [ "field"; "type"; "val"; "instance" ] member.kind ~equal:String.equal)

  (** The innermost of [members] whose text contains [loc]. *)
  let innermost (members : member list) (loc : Loc.t) =
    List.filter members ~f:(fun m -> attributable m && contains m.extent loc)
    |> List.min_elt ~compare:(fun m1 m2 -> Int.compare (size m1.extent) (size m2.extent))

  let status_to_string = function
    | Verified -> "verified"
    | Pending -> "pending"
    | Skipped -> "skipped"
    | Timeout -> "timeout"
    | Failed -> "failed"

  let of_outcome : outcome -> status = function
    | Cached | Verified -> Verified
    | Pending -> Pending
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
        (fst (List.hd_exn same), worst))

  (** Each of [members] with its status, if it has one, and the members that the [groups]
      inherit, given the [results] of the checked procedures, and whether the status is
      only from the cache. A checked member without a result of its own was skipped if the
      run was [aborted]. None has a status if nothing was checked. *)
  let statuses ~aborted (members : member list) groups
      (results : (procedure * outcome) list) =
    let attributed =
      List.filter_map results ~f:(fun (proc, outcome) ->
          Option.map (innermost members proc.proc_loc) ~f:(fun m ->
              (m, proc.proc_loc, outcome)))
    in
    let status member =
      let own = List.filter attributed ~f:(fun (m, _, _) -> phys_equal m member) in
      let worst =
        List.map own ~f:(fun (_, _, outcome) -> outcome)
        |> List.max_elt ~compare:compare_outcome
      in
      let checked_itself =
        List.exists own ~f:(fun (_, loc, _) -> Loc.equal loc member.name_loc)
      in
      match worst with
      | _ when List.is_empty results -> (None, false)
      | Some ((Failed | Timeout | Pending) as outcome) ->
          (Some (of_outcome outcome), false)
      | _ when aborted && member.checked && not checked_itself -> (Some Skipped, false)
      | Some ((Cached | Verified) as outcome) ->
          (Some Verified, [%compare.equal: outcome] outcome Cached)
      | None -> (None, false)
    in
    List.map members ~f:(fun member ->
        let status, cached = status member in
        (member, status, cached))
    @ List.map (inherited_statuses members groups results) ~f:(fun (member, outcome) ->
        (member, Some (of_outcome outcome), [%compare.equal: outcome] outcome Cached))

  let nested_in (group : group) (member : member) =
    String.is_prefix member.name ~prefix:(group.group_name ^ ".")

  (** The worst status of the members nested in [group], and how many have each status.
      Named assertions and invariants are counted with the members they are in. *)
  let summary (statuses : (member * status option) list) (group : group) =
    let nested =
      List.filter_map statuses ~f:(fun (member, status) ->
          if
            nested_in group member
            && not (List.mem [ "assertion"; "invariant" ] member.kind ~equal:String.equal)
          then status
          else None)
    in
    Option.map (List.max_elt nested ~compare:compare_status) ~f:(fun worst ->
        let counts =
          List.sort_and_group nested ~compare:compare_status
          |> List.map ~f:(fun same ->
              (status_to_string (List.hd_exn same), `Int (List.length same)))
        in
        (worst, counts))

  (** The text of [group]: its name and the members nested in it in the same file. *)
  let group_extent members (group : group) =
    List.fold members ~init:group.group_loc ~f:(fun extent member ->
        if
          nested_in group member
          && String.equal (Loc.file_name member.extent) (Loc.file_name extent)
        then Loc.merge extent member.extent
        else extent)

  (** Every member, module and named assertion, with its status when it has one. *)
  let to_json ~aborted members groups results : Yojson.Safe.t =
    let statuses = statuses ~aborted members groups results in
    let entry loc extent name kind status extra =
      `Assoc
        (Err.loc_to_lsp_fields loc
        @ [
            ("name", `String name);
            ("kind", `String kind);
            ("extent", `Assoc (Err.range_lsp_fields extent));
          ]
        @ Option.value_map status ~default:[] ~f:(fun status ->
            [ ("status", `String (status_to_string status)) ])
        @ extra)
    in
    let flag name b = if b then [ (name, `Bool true) ] else [] in
    `List
      (List.map statuses ~f:(fun (member, status, cached) ->
           entry member.name_loc member.extent member.name member.kind status
             (flag "inherited" member.inherited
             @ flag "checked" member.checked @ flag "cached" cached))
      @ List.map groups ~f:(fun group ->
          let summary =
            summary
              (List.map statuses ~f:(fun (member, status, _) -> (member, status)))
              group
          in
          entry group.group_loc (group_extent members group) group.group_name
            group.group_kind (Option.map summary ~f:fst)
            (Option.value_map summary ~default:[] ~f:(fun (_, counts) ->
                 [ ("counts", `Assoc counts) ]))))
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

exception Cancelled
(** Ends a run that was cancelled. *)

type cancellation = {
  input : Unix.file_descr;  (** Where a cancellation arrives. *)
  poll : unit -> bool;  (** Reads what arrived, and whether the run is cancelled. *)
}
(** How a run that a server answers learns that it is cancelled (see `raven --server`). *)

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
  cancellation : cancellation option;
  mutable last_poll : float;  (** When [cancellation] was last polled. *)
}

let create ?max_errors ?(collect_warnings = false) ?(reference_files = []) ?cancellation
    () =
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
    cancellation;
    last_poll = 0.;
  }

(** Raises [Cancelled] if the run is cancelled. *)
let check_cancelled d =
  match d.cancellation with
  | Some cancellation when cancellation.poll () -> raise Cancelled
  | _ -> ()

(** Like [check_cancelled], at most every 10 ms, for places passed often. *)
let check_cancelled_now_and_then d =
  if Option.is_some d.cancellation then begin
    let now = Unix.gettimeofday () in
    if Float.(now -. d.last_poll > 0.01) then begin
      d.last_poll <- now;
      check_cancelled d
    end
  end

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

type recorded = {
  recorded_annotations : Annotations.t list;
  recorded_warnings : Err.t list;
  recorded_origins : (string * string) list;
}
(** What a part of a run recorded besides errors, to record again in another run that
    skips that part (see [replay]). *)

type mark = int * int * (string, string) Hashtbl.t

let mark d : mark =
  (List.length d.annotations, List.length d.warnings, Hashtbl.copy d.origins)

(** What was recorded since [mark]. *)
let recorded_since d ((annotations, warnings, origins) : mark) =
  {
    recorded_annotations =
      List.take d.annotations (List.length d.annotations - annotations);
    recorded_warnings = List.take d.warnings (List.length d.warnings - warnings);
    recorded_origins =
      List.filter (Hashtbl.to_alist d.origins) ~f:(fun (member, _) ->
          not (Hashtbl.mem origins member));
  }

let replay d recorded =
  d.annotations <- recorded.recorded_annotations @ d.annotations;
  d.warnings <- recorded.recorded_warnings @ d.warnings;
  List.iter recorded.recorded_origins ~f:(fun (key, data) ->
      Hashtbl.set d.origins ~key ~data)

let set_origin d ~member origin = Hashtbl.set d.origins ~key:member ~data:origin
let origin d ~member ~default = Option.value (Hashtbl.find d.origins member) ~default
let annotations_to_json d = Annotations.all_to_json d.annotations

let set_members d (members, groups) =
  d.members <- members;
  d.groups <- groups

let record_result d proc outcome = d.results <- (proc, outcome) :: d.results

(** The members with their statuses, those of the [pending] procedures still to be
    checked. *)
let members_to_json ?(pending = []) d =
  MemberStatus.to_json ~aborted:d.aborted d.members d.groups
    (List.map pending ~f:(fun proc ->
         (proc, (MemberStatus.Pending : MemberStatus.outcome)))
    @ d.results)

let record_reference d reference = d.references <- reference :: d.references

(** Whether the names used at [loc] are collected. *)
let collects_references d loc =
  List.mem d.reference_files (Loc.file_name loc) ~equal:String.equal

let references_to_json d = References.to_json ~files:d.reference_files d.references
