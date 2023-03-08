open Base
open Util
open Frontend
open Error
open Backend

let greeting = "Raven version " ^ Config.version ^ "\n"

let usage_message =
  greeting ^ "\nUsage:\n  "
  ^ (Sys.get_argv ()).(0)
  ^ " <input file> [options]\n"

let cmd_line_error msg =
  Stdlib.Arg.usage (Stdlib.Arg.align Config.cmd_options_spec) usage_message;
  failwith ("Command line option error: " ^ msg)

let type_checking_enabled = true

let parse_and_print lexbuf =
  let s = Parser.main Lexer.token lexbuf in
  (*Stdio.printf !"%{Ast.Stmt}\n" s*)
  let _ = Smt_solver.init () in
  let processed_ast, tbl = Process_ast.start_processing s in
  match tbl with
  | [ _ ] -> Stdio.printf "SymbolTbl: \n%s" (Process_ast.SymbolTbl.to_string tbl);
    Ast.Module.print_verbose Stdio.stdout processed_ast;
    Stdio.print_endline "";

    Module_checker.check_module processed_ast tbl;


  | _ -> raise (Generic_Error "SymbolTbl should be empty")

let parse_program filename =
  let inx = Stdio.In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  Lexer.set_file_name lexbuf filename;
  let _ =
    try parse_and_print lexbuf
    with Parser.Error ->
      Stdio.In_channel.close inx;
      let err_pos = lexbuf.lex_curr_p in
      Error.syntax_error (Loc.make err_pos err_pos) None
  in
  Stdio.In_channel.close inx

let () =
  Backtrace.Exn.set_recording true;
  let main_file = ref "" in
  let set_main_file s = main_file := s in
  try
    Stdlib.Arg.parse Config.cmd_options_spec set_main_file usage_message;
    (*Debug.info (fun () -> greeting);*)
    if String.equal !main_file "" then cmd_line_error "input file missing"
    else Error.set_main_file !main_file; parse_program !main_file
  with
  | Sys_error s | Failure s ->
      (*let bs = if Debug.is_debug 0 then Printexc.get_backtrace () else "" in*)
      Stdio.prerr_endline ("Error: " ^ s);
      Stdio.prerr_endline "";
      Stdio.prerr_endline ("---------");
      Stdio.prerr_endline "";
      Stdio.prerr_endline (Backtrace.to_string (Backtrace.Exn.most_recent ()));
      Stdlib.exit 1
  | Error.Msg _ as e ->
      Stdio.prerr_endline (Error.to_string e);
      Stdio.prerr_endline "";
      Stdio.prerr_endline ("---------");
      Stdio.prerr_endline "";
      Stdio.prerr_endline (Backtrace.to_string (Backtrace.Exn.most_recent ()));
      Stdlib.exit 1
