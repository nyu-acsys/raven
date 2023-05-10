(** Error messages and exceptions *)

open Base

exception Msg of Loc.t * string
exception Generic_Error of string

let main_file = ref ""
let set_main_file s = main_file := s

let fail loc msg = raise (Msg (loc, msg))

let print_file_line line_num loc = 
  let rec in_channel_line ic (line_num: int) =
    let next_line = (match (Stdio.In_channel.input_line ic) with 
    | None -> ("Cannot print line " ^ (Int.to_string line_num) ^ ", location: " ^ Loc.to_string loc)
    | Some s -> s)

    in

    if line_num = 0 then
      next_line
    else 
      if line_num > 0 then
        in_channel_line ic (line_num-1)
      else
        "Cannot print line " ^ (Int.to_string line_num) ^ "; negative line_num found."


  in

  let ic = Stdio.In_channel.create !main_file in 
    Stdio.printf "%d | %s\n" line_num (in_channel_line ic (line_num - 1))

let print_error_loc (loc: Loc.t) =
  Stdio.printf "\n";

  let line_num1 = (loc.loc_start.pos_lnum) in
  let line_num2 = (loc.loc_end.pos_lnum) in
  let _ = List.map (List.range line_num1 (1+line_num2)) ~f:(fun line_num -> print_file_line line_num loc) in

  Stdio.printf "%s%s\n" (String.make (String.length (Int.to_string line_num1) + 2 + loc.loc_start.pos_cnum - loc.loc_start.pos_bol) ' ') (String.make (1 + loc.loc_end.pos_cnum - loc.loc_start.pos_cnum) '^');
  Stdio.print_endline ""

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
                                                 
let error loc msg = print_error_loc loc; fail loc @@ "Error: " ^ msg

let error_simple msg = fail Loc.dummy @@ "Error: " ^ msg

let lexical_error loc msg = print_error_loc loc; fail loc @@ "Lexical Error: " ^ msg

let unsupported_error loc msg = print_error_loc loc; fail loc @@ "Unsupported Feature Error: " ^ msg

let type_error loc msg = print_error_loc loc; fail loc @@ "Type Error: " ^ msg
                                                                             
let syntax_error loc msg_opt = 
  match msg_opt with 
  | Some msg -> print_error_loc loc; fail loc @@ "Syntax Error: " ^ msg
  | None -> print_error_loc loc; fail loc "Syntax Error"

let redeclaration_error loc name =
  print_error_loc loc; 
   fail loc (Printf.sprintf !"Identifier %{String} has already been declared in this scope." name)


let smt_error msg = fail Loc.dummy @@ "SMT Fail: " ^ msg
