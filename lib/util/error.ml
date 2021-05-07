(** Error messages and exceptions *)

open Base

exception Msg of Loc.t * string

let fail loc msg = raise (Msg (loc, msg))
    
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

(** Predefined error messags *)

let error loc msg = fail loc @@ "Error: " ^ msg

let lexical_error loc = fail loc "Lexical Error"

let type_error loc msg = fail loc @@ "Type Error: " ^ msg


let syntax_error loc msg_opt = 
  match msg_opt with 
  | Some msg -> fail loc @@ "Syntax Error: " ^ msg
  | None -> fail loc "Syntax Error"

let redeclaration_error loc name =
   fail loc (Printf.sprintf !"Identifier %{String} has already been declared in this scope." name)
