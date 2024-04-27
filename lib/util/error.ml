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
exception Generic_Error of string

let fail ?(lbl = Generic) loc msg = raise (Msg [lbl, loc, msg])

let fail_with errors = raise (Msg errors)

let to_string (kind, (loc: Loc.t), msg) =
  let label =
    kind |>
    error_kind_to_string |>
    fun lbl -> Fmt.to_to_string (fun ppf lbl -> Fmt.pf ppf "%a: " Fmt.(styled Logs_fmt.err_style string) lbl) lbl
  in
  if Loc.(loc = Loc.dummy) then
    Printf.sprintf !"%{String}%{String}" label msg
  else
    (*if !Config.flycheck_mode 
          then Printf.sprintf "%s:%s" (flycheck_string_of_src_pos pos) msg*)
    Printf.sprintf !"%{Loc}%{String}%{String}." loc label msg
    
(** Predefined error messags *)

let internal_error loc msg = fail loc ~lbl:Internal msg

let error loc msg = fail loc ~lbl:Generic msg

let error_simple msg = fail Loc.dummy msg

let lexical_error loc msg = fail loc ~lbl:Lexical msg

let unsupported_error loc msg = fail loc ~lbl:Unsupported msg

let type_error loc msg = fail loc ~lbl:Type msg
                                                                             
let syntax_error loc msg = fail loc ~lbl:Syntax msg

let redeclaration_error loc name =
  error loc (Printf.sprintf !"Identifier %{String} has already been declared in this scope" name)

let verification_error loc msg = fail loc ~lbl:Verification msg
