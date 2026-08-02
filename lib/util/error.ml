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

let error_kind_to_lsp_string = function
  | Generic -> "Generic"
  | Lexical -> "Lexical"
  | Syntax -> "Syntax"
  | Type -> "Type"
  | Internal -> "Internal"
  | Unsupported -> "Unsupported"
  | Verification -> "Verification"
  | RelatedLoc -> "RelatedLoc"


let error_kind_to_string = function
  | Generic -> "Error"
  | Lexical -> "Lexical Error"
  | Syntax -> "Syntax Error"
  | Type -> "Type Error"
  | Internal -> "Internal Error"
  | Unsupported -> "Unsupported Error"
  | Verification -> "Verification Error"
  | RelatedLoc -> "Related Location"

type t = error_kind * Loc.t * String.t

exception Msg of t list

let fail ?(lbl = Generic) loc msg = raise (Msg [ (lbl, loc, msg) ])
let fail_with errors = raise (Msg errors)

let to_string (kind, (loc : Loc.t), msg) =
  let label =
    kind |> error_kind_to_string |> fun lbl ->
    Fmt.to_to_string
      (fun ppf lbl ->
        Fmt.pf ppf "%a: " Fmt.(styled Logs_fmt.err_style string) lbl)
      lbl
  in
  if Loc.(loc = Loc.dummy) then Printf.sprintf !"%{String}%{String}" label msg
  else
    (*if !Config.flycheck_mode
          then Printf.sprintf "%s:%s" (flycheck_string_of_src_pos pos) msg*)
    Printf.sprintf !"%{Loc}%{String}%{String}." loc label msg

let to_lsp_json (kind, (loc : Loc.t), msg) =
  let r = Str.regexp "\n" in
  let split_msg = Str.split r msg in
  let file = Loc.file_name loc in
  (* A location inside an embedded library source names no file on disk, so an editor
     cannot open it as an ordinary path. Say so explicitly ("library": true) and, when
     this binary is running inside the checkout it was built from, hand over the real
     path as well ("path"). A client can then open the actual source when there is one
     and fall back to serving the embedded text read-only when there isn't -- rather
     than resolving a library path against the user's own project and missing. *)
  let library_fields =
    if not (Loc.is_library_source file) then []
    else
      ("library", `Bool true)
      :: (match Loc.library_real_path file with
          | Some path -> [ ("path", `String path) ]
          | None -> [])
  in
  let json = `Assoc ([
    ("file", `String file);
    ("start_line", `Int (Loc.start_line loc));
    ("start_col", `Int (Loc.start_col loc));
    ("end_line", `Int (Loc.end_line loc));
    ("end_col", `Int (Loc.end_col loc));
    ("kind", `String (error_kind_to_lsp_string kind));
    ("message", `List (List.map split_msg ~f:(fun s -> `String s)))
  ] @ library_fields) in

  json

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
    (Printf.sprintf
       !"Identifier %{String} has already been declared in this scope"
       name)

let verification_error loc msg = fail loc ~lbl:Verification msg
