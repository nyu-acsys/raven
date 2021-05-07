open Base
open Util
open Frontend
  
let greeting =
  "Raven version " ^ Config.version ^ "\n"
                                              
let usage_message =
  greeting ^
  "\nUsage:\n  " ^ (Sys.get_argv ()).(0) ^ 
  " <input file> [options]\n"

let cmd_line_error msg =
  Stdlib.Arg.usage (Stdlib.Arg.align Config.cmd_options_spec) usage_message;
  failwith ("Command line option error: " ^ msg)
    
let parse_and_print lexbuf =
  let s = Parser.main Lexer.token lexbuf in
  (*Stdio.printf !"%{Ast.Stmt}\n" s*)
  Ast.Module.print Stdio.stdout s;
  Stdio.print_endline ""

let parse_program filename =
  let inx = Stdio.In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  Lexer.set_file_name lexbuf filename;
  let _ =
    try
      parse_and_print lexbuf;
    with
    | Parser.Error ->
        Stdio.In_channel.close inx;
        let err_pos = lexbuf.lex_curr_p in
        Error.syntax_error (Loc.make err_pos err_pos) None
  in
  Stdio.In_channel.close inx

let () =
  let main_file = ref "" in
  let set_main_file s =
    main_file := s;
  in
  try
    Stdlib.Arg.parse Config.cmd_options_spec set_main_file usage_message;
    (*Debug.info (fun () -> greeting);*)
    if String.equal !main_file ""
    then cmd_line_error "input file missing"
    else 
      parse_program !main_file
  with 
  | Sys_error s | Failure s -> 
      (*let bs = if Debug.is_debug 0 then Printexc.get_backtrace () else "" in*)
      Stdio.prerr_endline ("Error: " ^ s); Stdlib.exit 1
  | Error.Msg _ as e ->
      Stdio.prerr_endline (Error.to_string e);
      Stdlib.exit 1
