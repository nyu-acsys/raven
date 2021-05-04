(** Error messages and exceptions *)

open Base

exception Msg of Loc.t * string

let lexical_error pos = raise (Msg (pos, "Lexical Error"))

let syntax_error pos msg_opt = 
  match msg_opt with 
  | Some msg -> raise (Msg (pos, "Syntax Error: " ^ msg))
  | None -> raise (Msg (pos, "Syntax Error"))

let type_error loc msg = raise (Msg (loc, "Type Error: " ^ msg))

let error loc msg = raise (Msg (loc, "Error: " ^ msg))

let to_string (loc: Loc.t) msg = 
  if Loc.(loc = Loc.dummy)
  then msg 
  else
    (*if !Config.flycheck_mode 
    then Printf.sprintf "%s:%s" (flycheck_string_of_src_pos pos) msg*)
    Printf.sprintf !"%{Loc}:\n%{String}" loc msg

let to_string = function
  | Msg (loc, msg) -> to_string loc msg      
  | _ -> raise (Invalid_argument "ProgError.to_string: expected a program error exception")

let print loc msg = Stdio.print_endline (to_string (Msg (loc, msg)))

let mk_trace_info msg = "Trace Information: " ^ msg

let mk_error_info msg = "Related Location: " ^ msg

