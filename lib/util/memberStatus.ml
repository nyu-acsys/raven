(** The verification status of the program's members, printed for an editor by `--lsp-mode
    --lsp-annotations`. A member's status is the worst outcome of the procedures checked
    for it: its own, and those that elaboration and lowering generate from its loops,
    contract and quantifiers, which lie within its text. A module summarizes the status of
    the members nested in it. *)

module Err = Error
open Base

(** The outcome of checking a procedure, from best to worst. *)
type outcome = Verified | Timeout | Failed [@@deriving compare]

(** The status of a member, from best to worst. *)
type status = Verified | Skipped | Timeout | Failed [@@deriving compare]

type member = {
  name : string;  (** Qualified by the modules it is nested in. *)
  kind : string;
  name_loc : Loc.t;
  extent : Loc.t;  (** Its name, contract and body. *)
  checked : bool;  (** Whether it is checked itself: a procedure or lemma with a body. *)
  inherited : bool;
      (** Whether a module inherits it, such as a lemma for an axiom of its interface. *)
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
  |> List.sort_and_group ~compare:(fun (m1, _) (m2, _) -> String.compare m1.name m2.name)
  |> List.map ~f:(fun same ->
      let worst =
        List.map same ~f:snd |> List.max_elt ~compare:compare_outcome |> Option.value_exn
      in
      (fst (List.hd_exn same), of_outcome worst))

(** The status of each of [members], and of those that the [groups] inherit, given the
    [results] of the checked procedures. A checked member without a result of its own was
    skipped if the run was [aborted]. There are none if nothing was checked. *)
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
