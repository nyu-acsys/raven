(** Error messages and exceptions *)

open Base

type error_kind =
  | Generic
  | Lexical
  | Syntax
  | Type
  | Internal
  | Unsupported
  | Verification
  | RelatedLoc
  | Warning

let error_kind_to_lsp_string = function
  | Generic -> "Generic"
  | Lexical -> "Lexical"
  | Syntax -> "Syntax"
  | Type -> "Type"
  | Internal -> "Internal"
  | Unsupported -> "Unsupported"
  | Verification -> "Verification"
  | RelatedLoc -> "RelatedLoc"
  | Warning -> "Warning"

let error_kind_to_string = function
  | Generic -> "Error"
  | Lexical -> "Lexical Error"
  | Syntax -> "Syntax Error"
  | Type -> "Type Error"
  | Internal -> "Internal Error"
  | Unsupported -> "Unsupported Error"
  | Verification -> "Verification Error"
  | RelatedLoc -> "Related Location"
  | Warning -> "Warning"

type t = error_kind * Loc.t * String.t

let recorded_warnings : t list ref = ref []
let collect_warnings = ref false

let configure_warnings ~collect =
  recorded_warnings := [];
  collect_warnings := collect

let warnings () = List.rev !recorded_warnings

let warning loc msg =
  if !collect_warnings then recorded_warnings := (Warning, loc, msg) :: !recorded_warnings
  else Logs.warn (fun m -> m "%s%s" (Loc.to_string loc) msg)

exception Msg of t list

let fail ?(lbl = Generic) loc msg = raise (Msg [ (lbl, loc, msg) ])
let fail_with errors = raise (Msg errors)

(** Merges the diagnostics in [diags] that have the same primary error, collecting their
    related locations, e.g. those of the conjuncts of one postcondition that may not hold.
*)
let merge_diagnostics (diags : t list list) : t list list =
  let add merged = function
    | [] -> merged
    | primary :: related -> (
        match List.Assoc.find merged primary ~equal:Poly.equal with
        | Some known ->
            let fresh =
              List.filter related ~f:(fun r -> not (List.mem known r ~equal:Poly.equal))
            in
            List.Assoc.add merged primary (known @ fresh) ~equal:Poly.equal
        | None -> (primary, related) :: merged)
  in
  List.fold diags ~init:[] ~f:add
  |> List.rev_map ~f:(fun (primary, related) -> primary :: related)

(** Orders diagnostics by the location of their primary error. A diagnostic is a primary
    error followed by its related locations. *)
let sort_diagnostics (diags : t list list) : t list list =
  let primary_loc = function (_, loc, _) :: _ -> loc | [] -> Loc.dummy in
  List.stable_sort diags ~compare:(fun d1 d2 ->
      Loc.compare (primary_loc d1) (primary_loc d2))

let to_string (kind, (loc : Loc.t), msg) =
  let label =
    kind |> error_kind_to_string |> fun lbl ->
    Fmt.to_to_string
      (fun ppf lbl -> Fmt.pf ppf "%a: " Fmt.(styled Logs_fmt.err_style string) lbl)
      lbl
  in
  if Loc.(loc = Loc.dummy) then Printf.sprintf !"%{String}%{String}" label msg
  else
    (*if !Config.flycheck_mode
          then Printf.sprintf "%s:%s" (flycheck_string_of_src_pos pos) msg*)
    Printf.sprintf !"%{Loc}%{String}%{String}." loc label msg

(** The fields marking a location in an embedded library source, in the JSON of
    `--lsp-mode`. A location inside an embedded library source names no file on disk, so
    an editor cannot open it as an ordinary path. Say so explicitly ("library": true) and,
    when this binary is running inside the checkout it was built from, hand over the real
    path as well ("path"). A client can then open the actual source when there is one and
    fall back to serving the embedded text read-only when there isn't -- rather than
    resolving a library path against the user's own project and missing. *)
let library_lsp_fields (loc : Loc.t) =
  let file = Loc.file_name loc in
  if not (Loc.is_library_source file) then []
  else
    ("library", `Bool true)
    ::
    (match Loc.library_real_path file with
    | Some path -> [ ("path", `String path) ]
    | None -> [])

(** The fields locating [loc] in the JSON of `--lsp-mode`, without [library_lsp_fields].
*)
let range_lsp_fields (loc : Loc.t) =
  [
    ("file", `String (Loc.file_name loc));
    ("start_line", `Int (Loc.start_line loc));
    ("start_col", `Int (Loc.start_col loc));
    ("end_line", `Int (Loc.end_line loc));
    ("end_col", `Int (Loc.end_col loc));
  ]

(** The fields locating [loc] in the JSON of `--lsp-mode`. *)
let loc_to_lsp_fields (loc : Loc.t) = range_lsp_fields loc @ library_lsp_fields loc

let to_lsp_json (kind, (loc : Loc.t), msg) =
  let r = Str.regexp "\n" in
  let split_msg = Str.split r msg in
  `Assoc
    (range_lsp_fields loc
    @ [
        ("kind", `String (error_kind_to_lsp_string kind));
        ("message", `List (List.map split_msg ~f:(fun s -> `String s)));
      ]
    @ library_lsp_fields loc)

let errors_to_lsp_string errs =
  let json_list = List.map ~f:to_lsp_json errs in
  let json_errs = `List json_list in
  Yojson.Safe.to_string json_errs

(** Predefined error messags *)

let internal_error loc msg = fail loc ~lbl:Internal msg
let error loc msg = fail loc ~lbl:Generic msg
let error_simple msg = fail Loc.dummy msg
let lexical_error loc msg = fail loc ~lbl:Lexical msg
let unsupported_error loc msg = fail loc ~lbl:Unsupported msg
let type_error loc msg = fail loc ~lbl:Type msg
let syntax_error loc msg = fail loc ~lbl:Syntax msg

let redeclaration_error loc name =
  error loc
    (Printf.sprintf !"Identifier %{String} has already been declared in this scope" name)

let verification_error loc msg = fail loc ~lbl:Verification msg
