(** Counterexamples: the values of a procedure's variables where one of its checks fails,
    and of the fields of the references among them, read from the solver's model and shown
    in source terms. *)

open Base
open Ast
open Util
module Sexp = Sexplib.Sexp

type query = {
  variables : (string * expr) list;  (** By their source names. *)
  references : (string * expr) list;  (** The variables that are references. *)
  heaps : (string * expr) list;  (** By the names of their fields. *)
}
(** What a counterexample asks the model for, from the current versions of the variables
    in [state] and the field heaps among them, whose fields [heap_field] names. *)

let query ~(heap_field : string -> string option) (state : var_decl list) : query =
  let named (var : var_decl) = (Ident.name var.var_name, Expr.from_var_decl var) in
  let generated (var : var_decl) = String.contains (Ident.name var.var_name) '$' in
  let variables = List.filter state ~f:(fun var -> not (generated var)) in
  {
    variables = List.map variables ~f:named;
    references =
      List.filter_map variables ~f:(fun var ->
          Option.some_if (Type.equal var.var_type Type.ref) (named var));
    heaps =
      List.filter_map state ~f:(fun var ->
          Option.map
            (heap_field (Ident.name var.var_name))
            ~f:(fun field -> (field, Expr.from_var_decl var)));
  }

(** The terms of [query] in the order [render] expects their values: the variables, null,
    then each field of each reference. *)
let terms (query : query) : expr list =
  List.map query.variables ~f:snd
  @ [ Expr.mk_null () ]
  @ List.concat_map query.references ~f:(fun (_, reference) ->
      List.map query.heaps ~f:(fun (_, heap) -> Expr.mk_maplookup heap reference))

(** The name of a declared symbol without the modules it is in. *)
let base_name name =
  match String.rsplit2 name ~on:'.' with Some (_, base) -> base | None -> name

(** A number without the trailing [.0] of a whole real. *)
let number text = Option.value (String.chop_suffix text ~suffix:".0") ~default:text

(** [value] with the bindings of its [let]s substituted. *)
let rec expand_lets ?(bindings = []) (value : Sexp.t) : Sexp.t =
  match value with
  | Atom atom ->
      Option.value (List.Assoc.find bindings atom ~equal:String.equal) ~default:value
  | List [ Atom "let"; List definitions; body ] ->
      let bindings =
        List.fold definitions ~init:bindings ~f:(fun acc -> function
          | List [ Atom name; definition ] ->
              (name, expand_lets ~bindings definition) :: acc
          | _ -> acc)
      in
      expand_lets ~bindings body
  | List values -> List (List.map values ~f:(expand_lets ~bindings))

(** [value] in source terms, with the references named by [reference]. *)
let rec render ~(reference : string -> string option) (value : Sexp.t) : string =
  let render = render ~reference in
  match value with
  | Atom atom -> (
      match reference atom with
      | Some name -> name
      | None ->
          if Char.is_digit atom.[0] then number atom
          else if String.equal atom "true" || String.equal atom "false" then atom
          else base_name atom)
  | List [ Atom "-"; x ] -> "-" ^ render x
  | List [ Atom "/"; x; y ] -> render x ^ "/" ^ render y
  (* Maps, sets and sequences come as arrays, which are not shown yet. *)
  | List (Atom ("store" | "_" | "lambda") :: _) | List (List _ :: _) -> "…"
  | List (Atom constructor :: args) ->
      Printf.sprintf "%s(%s)" (base_name constructor)
        (String.concat ~sep:", " (List.map args ~f:render))
  | List [] -> "()"

(** A field's value: for a fraction, its value and permission, or [None] without one. *)
let render_field ~reference (value : Sexp.t) : string option =
  match value with
  | List [ Atom chunk; v; p ] when String.equal (base_name chunk) "frac_chunk" ->
      Some
        (Printf.sprintf "%s (permission %s)" (render ~reference v) (render ~reference p))
  | Atom null when String.equal (base_name null) "frac_null" -> None
  | value -> Some (render ~reference value)

(** The counterexample of [query] given the [values] of its [terms]: one line per
    variable, and per field of a reference that the procedure has permission to. *)
let lines (query : query) (values : Sexp.t list) : string list =
  let values = List.map values ~f:(fun value -> expand_lets value) in
  let variable_values, rest = List.split_n values (List.length query.variables) in
  match rest with
  | [] -> []
  | null_value :: field_values ->
      (* The references by the order they first appear in, as ref#1, ref#2, ..., which
         cannot be the name of a variable. *)
      let names = Hashtbl.create (module String) in
      let atom_of = function Sexp.Atom atom -> Some atom | List _ -> None in
      Option.iter (atom_of null_value) ~f:(fun null ->
          Hashtbl.set names ~key:null ~data:"null");
      List.iter2_exn query.variables variable_values ~f:(fun (_, term) value ->
          match (Type.equal (Expr.to_type term) Type.ref, atom_of value) with
          | true, Some atom when not (Hashtbl.mem names atom) ->
              Hashtbl.set names ~key:atom
                ~data:(Printf.sprintf "ref#%d" (Hashtbl.length names))
          | _ -> ());
      let reference = Hashtbl.find names in
      let variables =
        List.map2_exn query.variables variable_values ~f:(fun (name, _) value ->
            Printf.sprintf "%s = %s" name (render ~reference value))
      in
      let fields =
        if List.is_empty query.heaps then []
        else
          List.concat_map
            (List.zip_exn query.references
               (List.chunks_of field_values ~length:(max 1 (List.length query.heaps))))
            ~f:(fun ((reference_name, _), values) ->
              List.filter_map (List.zip_exn query.heaps values)
                ~f:(fun ((field, _), value) ->
                  Option.map (render_field ~reference value) ~f:(fun shown ->
                      Printf.sprintf "%s.%s = %s" reference_name field shown)))
      in
      variables @ fields

(** The diagnostic entry of a counterexample, for the error before it. *)
let to_error ~certain (lines : string list) : Error.t =
  (Counterexample { certain }, Loc.dummy, String.concat ~sep:"\n" lines)
