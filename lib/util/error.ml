(** Error messages and exceptions *)

open Base

type t = String.t option * Loc.t * String.t

exception Msg of t
exception Generic_Error of string

let fail ?lbl loc msg = raise (Msg (lbl, loc, msg))

let to_string (label, (loc: Loc.t), msg) =
  let label =
    label |>
    Option.map ~f:(fun lbl -> Fmt.to_to_string (fun ppf lbl -> Fmt.pf ppf "%a: " Fmt.(styled Logs_fmt.err_style string) lbl) lbl) |>
    Option.value ~default:""
  in
  if Loc.(loc = Loc.dummy) then
    Printf.sprintf !"%{String}%{String}" label msg
  else
    (*if !Config.flycheck_mode 
    then Printf.sprintf "%s:%s" (flycheck_string_of_src_pos pos) msg*)
    Printf.sprintf !"%{Loc}%{String}%{String}" loc label msg

(*let print loc msg = Stdio.print_endline (to_string (Msg (loc, msg)))*)

let mk_trace_info msg = "Trace Information: " ^ msg

let mk_error_info msg = "Related Location: " ^ msg

(** Predefined error messags *)
                                                 
let error loc msg = fail loc ~lbl:"Error" msg

let error_simple msg = fail Loc.dummy msg

let lexical_error loc msg = fail loc ~lbl:"Lexical Error" msg

let unsupported_error loc msg = fail loc ~lbl:"Unsupported Feature Error" msg

let type_error loc msg = fail loc ~lbl:"Type Error" msg
                                                                             
let syntax_error loc msg_opt = 
  match msg_opt with 
  | Some msg -> fail loc ~lbl:"Syntax Error" msg
  | None -> fail loc "Syntax Error"

let redeclaration_error loc name =
  error loc (Printf.sprintf !"Identifier %{String} has already been declared in this scope." name)

let smt_error msg = fail Loc.dummy ~lbl:"SMT Error" msg
