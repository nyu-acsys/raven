(** What a run reports besides its result: the errors recorded at recovery points, the
    warnings, and the annotations and the status of members for an editor. The driver
    creates one per run and every phase adds to it. It is mutable, so that a recovery
    point further out, which rolls back the state of the computation that failed, keeps
    what was recorded. *)

module Err = Error
open Base

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
  mutable results : (MemberStatus.procedure * MemberStatus.outcome) list;
      (** The outcomes of the checked procedures. *)
  origins : (string, string) Hashtbl.t;
      (** The interface each inherited member originates from, by the qualified name of
          the member in the module that inherits it. *)
}

let create ?max_errors ?(collect_warnings = false) () =
  {
    errors = [];
    aborted = false;
    max_errors;
    collect_warnings;
    warnings = [];
    annotations = [];
    members = [];
    groups = [];
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
