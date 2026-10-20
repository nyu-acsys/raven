(** Counterexamples: the values of a procedure's variables where one of its checks fails,
    and of the fields of the references among them, read from the solver's model and shown
    in source terms. *)

open Base
open Ast
open Util
module Sexp = Sexplib.Sexp

type branch = { id : int; stmt_loc : Loc.t; test : expr; arm : (int * bool) option }
(** A conditional the checker entered: its test, and the arm of another it is in, as the
    conditional's [id] and whether it is the [then] arm. *)

type sequence = { name : string; term : expr; length : qual_ident; index : qual_ident }
(** A variable whose type has the functions of a sequence, whose elements are read with
    them, since the type itself is opaque to the solver. *)

type query = {
  variables : (string * expr) list;  (** By their source names. *)
  references : (string * expr) list;  (** The variables that are references. *)
  heaps : (string * expr) list;  (** By the names of their fields. *)
  sequences : sequence list;
  candidates : branch list;
      (** The conditionals entered before the check whose arms have rejoined, so that the
          model decides which arm the failing path took. *)
  arms : (int * bool) list;  (** The arms of the conditionals the check is in. *)
}
(** What a counterexample asks the model for, from the current versions of the variables
    in [state] and the field heaps among them, whose fields [heap_field] names; the
    [length] and [index] functions of a sequence type are given by [sequence_functions].
*)

let query ~(heap_field : string -> string option)
    ~(sequence_functions : type_expr -> (qual_ident * qual_ident) option)
    ~(branches : branch list) ~(arms : (int * bool) list) (state : var_decl list) : query
    =
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
    sequences =
      List.filter_map variables ~f:(fun var ->
          Option.map (sequence_functions var.var_type) ~f:(fun (length, index) ->
              {
                name = Ident.name var.var_name;
                term = Expr.from_var_decl var;
                length;
                index;
              }));
    candidates =
      List.filter (List.rev branches) ~f:(fun branch ->
          not (List.Assoc.mem arms branch.id ~equal:Int.equal));
    arms;
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
          if String.is_prefix atom ~prefix:"$tuple_" then "()"
          else if Char.is_digit atom.[0] then number atom
          else if String.equal atom "true" || String.equal atom "false" then atom
          else base_name atom)
  | List (Atom tuple :: args) when String.is_prefix tuple ~prefix:"$tuple_" ->
      Printf.sprintf "(%s)" (String.concat ~sep:", " (List.map args ~f:render))
  | List [ Atom "-"; x ] -> "-" ^ render x
  | List [ Atom "/"; x; y ] -> render x ^ "/" ^ render y
  | List [ Atom "store"; _; _; _ ] | List [ List [ Atom "as"; Atom "const"; _ ]; _ ] ->
      render_array ~reference value
  (* An array the model defines elsewhere, or as a function, is not shown. *)
  | List (Atom ("_" | "lambda") :: _) | List (List _ :: _) -> "…"
  | List (Atom constructor :: args) ->
      Printf.sprintf "%s(%s)" (base_name constructor)
        (String.concat ~sep:", " (List.map args ~f:render))
  | List [] -> "()"

(** An array given by updates of a constant one: a set as its elements, or all but some,
    and a map as its entries and the value elsewhere. *)
and render_array ~reference (value : Sexp.t) : string =
  let render = render ~reference in
  (* The entries, the last update of an index first, and the constant and its sort. *)
  let rec updates entries = function
    | Sexp.List [ Atom "store"; array; index; v ] ->
        let entries =
          if List.Assoc.mem entries index ~equal:Sexp.equal then entries
          else entries @ [ (index, v) ]
        in
        updates entries array
    | List [ List [ Atom "as"; Atom "const"; sort ]; constant ] ->
        Some (entries, constant, sort)
    | _ -> None
  in
  match updates [] value with
  | None -> "…"
  | Some (entries, constant, sort) -> (
      let is_set = match sort with List (Atom "Set" :: _) -> true | _ -> false in
      let members default =
        List.filter_map entries ~f:(fun (index, v) ->
            Option.some_if (not (Sexp.equal v default)) (render index))
        |> List.rev
      in
      match (is_set, constant) with
      | true, Atom "false" ->
          Printf.sprintf "{%s}" (String.concat ~sep:", " (members (Atom "false")))
      | true, _ -> (
          match members (Atom "true") with
          | [] -> "all"
          | excluded -> Printf.sprintf "all but {%s}" (String.concat ~sep:", " excluded))
      | false, _ ->
          let shown =
            List.rev_map entries ~f:(fun (index, v) ->
                Printf.sprintf "%s := %s" (render index) (render v))
          in
          Printf.sprintf "[%s]"
            (String.concat ~sep:", " (shown @ [ "else " ^ render constant ])))

(** A field's value: for a fraction, its value and permission, or [None] without one. *)
let render_field ~reference (value : Sexp.t) : string option =
  match value with
  | List [ Atom chunk; v; p ] when String.equal (base_name chunk) "frac_chunk" ->
      Some
        (Printf.sprintf "%s (permission %s)" (render ~reference v) (render ~reference p))
  | Atom null when String.equal (base_name null) "frac_null" -> None
  | value -> Some (render ~reference value)

(** The name of the type whose values the solver's sort [sort] holds: [Ref] for
    references, a module [M] for its rep type [M.T], as Raven writes it, and the functor
    for an instance the verifier generated. *)
let abstract_type (sort : string) : string =
  if String.equal sort "$Loc" then "Ref"
  else
    match String.substr_index sort ~pattern:"GenInst$$" with
    | Some at -> (
        let functor_name = String.drop_prefix sort (at + String.length "GenInst$$") in
        let functor_name =
          match String.substr_index functor_name ~pattern:"$$" with
          | Some until -> String.prefix functor_name until
          | None -> functor_name
        in
        (* The parts of its qualified name are joined by underscores. *)
        match String.rsplit2 functor_name ~on:'_' with
        | Some (_, base) -> base
        | None -> functor_name)
    | None -> (
        match String.chop_suffix sort ~suffix:".T" with
        | Some modul -> base_name modul
        | None -> base_name sort)

(** Names the solver's values of uninterpreted sorts, [<sort>!val!<n>], in [names] as
    [<type>#1], [<type>#2], ... by the order they are first shown, which no variable can
    be named. *)
let abstract_values (names : (string, string) Hashtbl.t) (atom : string) : string option =
  match Hashtbl.find names atom with
  | Some name -> Some name
  | None -> (
      match String.substr_index atom ~pattern:"!val!" with
      | None -> None
      | Some at ->
          let typ = abstract_type (String.prefix atom at) in
          let count =
            Hashtbl.count names ~f:(fun name -> String.is_prefix name ~prefix:(typ ^ "#"))
          in
          let name = Printf.sprintf "%s#%d" typ (count + 1) in
          Hashtbl.set names ~key:atom ~data:name;
          Some name)

(** The counterexample of [query] given the [values] of its [terms]: one line per
    variable, and per field of a reference that the procedure has permission to. *)
let lines ?(sequences = []) (query : query) (values : Sexp.t list) : string list =
  let values = List.map values ~f:(fun value -> expand_lets value) in
  let variable_values, rest = List.split_n values (List.length query.variables) in
  match rest with
  | [] -> []
  | null_value :: field_values ->
      let names = Hashtbl.create (module String) in
      (match null_value with
      | Atom null -> Hashtbl.set names ~key:null ~data:"null"
      | List _ -> ());
      let reference = abstract_values names in
      (* A sequence by its elements, and its length if not all are shown. *)
      let sequence name =
        List.find_map sequences ~f:(fun (sequence_name, length, elements) ->
            Option.some_if
              (String.equal sequence_name name)
              (let shown = List.map elements ~f:(render ~reference) in
               if List.length shown < length then
                 Printf.sprintf "[%s, …] (length %d)"
                   (String.concat ~sep:", " shown)
                   length
               else Printf.sprintf "[%s]" (String.concat ~sep:", " shown)))
      in
      let variables =
        List.map2_exn query.variables variable_values ~f:(fun (name, _) value ->
            Printf.sprintf "%s = %s" name
              (Option.value (sequence name) ~default:(render ~reference value)))
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

(** The number [value] stands for, if it is one. *)
let int_of (value : Sexp.t) =
  match value with
  | Atom atom -> Int.of_string_opt atom
  | List [ Atom "-"; Atom atom ] -> Option.map (Int.of_string_opt atom) ~f:Int.neg
  | List _ -> None

(** How many elements of a sequence are shown. *)
let max_elements = 10

(** Whether the source [if] statement [text] has an [else]: the word after the block of
    its [then] arm. *)
let has_else (text : string) : bool =
  match String.index text '{' with
  | None -> String.is_substring text ~substring:"else"
  | Some start ->
      let rec close i depth =
        if i >= String.length text then None
        else
          match text.[i] with
          | '{' -> close (i + 1) (depth + 1)
          | '}' -> if depth = 1 then Some i else close (i + 1) (depth - 1)
          | _ -> close (i + 1) depth
      in
      Option.value_map (close start 0) ~default:false ~f:(fun i ->
          String.is_prefix
            (String.lstrip (String.drop_prefix text (i + 1)))
            ~prefix:"else")

(** What the arm of [branch] that is taken is called, if it is a source [if] or [while]:
    lowering generates conditionals of its own. An [if] without [else] skips its [then]
    arm. *)
let arm_label (branch : branch) (taken : bool) : string option =
  Option.bind (Loc.source_text branch.stmt_loc) ~f:(fun text ->
      let text = String.lstrip text in
      if String.is_prefix text ~prefix:"if" then
        Some (if taken then "then" else if has_else text then "else" else "skipped")
      else if String.is_prefix text ~prefix:"while" then
        Some (if taken then "iterates" else "exits")
      else None)

(** Where to show the arm taken of [branch]: at its condition, if it has a location. *)
let branch_loc (branch : branch) : Loc.t =
  let test_loc = Expr.to_loc branch.test in
  if String.equal (Loc.file_name test_loc) (Loc.file_name branch.stmt_loc) then test_loc
  else branch.stmt_loc

(** The arms the failing path takes at the [candidates] of [query], given the values of
    their tests: of those whose enclosing arm is on the path, and are in the source. *)
let taken_branches (query : query) (test_values : Sexp.t list) : (Loc.t * string) list =
  let taken = Hashtbl.create (module Int) in
  List.iter query.arms ~f:(fun (id, arm) -> Hashtbl.set taken ~key:id ~data:arm);
  List.filter_map (List.zip_exn query.candidates test_values) ~f:(fun (branch, value) ->
      let on_path =
        match branch.arm with
        | None -> true
        | Some (id, arm) -> Option.equal Bool.equal (Hashtbl.find taken id) (Some arm)
      in
      match expand_lets value with
      | Atom (("true" | "false") as truth) when on_path ->
          let truth = String.equal truth "true" in
          Hashtbl.set taken ~key:branch.id ~data:truth;
          Option.map (arm_label branch truth) ~f:(fun label -> (branch_loc branch, label))
      | _ -> None)

type t = { lines : string list; branches : (Loc.t * string) list }
(** A counterexample: one line per value, and the arms its path takes. *)

(** The counterexample of [query] that the model gives through [get_values]: after the
    values of the [terms] and of the tests of the conditionals, the lengths of the
    sequences, then their first elements. A sequence whose functions the solver does not
    know is shown as its value. *)
let collect (query : query) ~(get_values : expr list -> Sexp.t list option) : t =
  let base = terms query in
  match get_values (base @ List.map query.candidates ~f:(fun branch -> branch.test)) with
  | None -> { lines = []; branches = [] }
  | Some values ->
      let values, test_values = List.split_n values (List.length base) in
      let call f args = Expr.mk_app ~typ:Type.any (Var f) args in
      let lengths =
        if List.is_empty query.sequences then None
        else get_values (List.map query.sequences ~f:(fun s -> call s.length [ s.term ]))
      in
      let lengths =
        Option.value_map lengths ~default:[] ~f:(fun lengths ->
            List.filter_map (List.zip_exn query.sequences lengths) ~f:(fun (s, length) ->
                Option.bind
                  (int_of (expand_lets length))
                  ~f:(fun n -> Option.some_if (n >= 0) (s, n))))
      in
      let element_terms =
        List.concat_map lengths ~f:(fun (s, n) ->
            List.init (min n max_elements) ~f:(fun i ->
                call s.index [ s.term; Expr.mk_int i ]))
      in
      let elements =
        if List.is_empty element_terms then Some []
        else
          Option.map (get_values element_terms) ~f:(List.map ~f:(fun v -> expand_lets v))
      in
      let sequences =
        match elements with
        | None -> []
        | Some elements ->
            List.folding_map lengths ~init:elements ~f:(fun remaining (s, n) ->
                let mine, rest = List.split_n remaining (min n max_elements) in
                (rest, (s.name, n, mine)))
      in
      {
        lines = lines ~sequences query values;
        branches = taken_branches query test_values;
      }

(** The diagnostic entries of a counterexample, for the error before them: its values, and
    the arm taken at each conditional on its path. *)
let to_errors ~certain (counterexample : t) : Error.t list =
  match counterexample.lines with
  | [] -> []
  | lines ->
      (Counterexample { certain }, Loc.dummy, String.concat ~sep:"\n" lines)
      :: List.map counterexample.branches ~f:(fun (loc, label) ->
          (Error.Branch, loc, label))
