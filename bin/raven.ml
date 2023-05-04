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


let parse_lib lexbuf =
  let s = Parser.lib Lexer.token lexbuf in

  let processed_lib_ast, tbl = Process_ast.start_processing s in

  let smtEnv, session = Checker.start_backend_checking processed_lib_ast tbl in

  tbl, smtEnv, session 

let parse_and_print lexbuf tbl smtEnv session =
  let s = Parser.main Lexer.token lexbuf in
  (*Stdio.printf !"%{Ast.Stmt}\n" s*)

  let processed_ast, tbl = Process_ast.start_processing ~tbl:tbl s in
  match tbl with
  | [ _ ; _ ] | [ _ ] -> 
    Stdio.printf "SymbolTbl: \n%s" (Process_ast.SymbolTbl.to_string tbl);
    Ast.Module.print_verbose Stdio.stdout processed_ast;
    Stdio.print_endline "\n\nFront-end processing successful.\n";

    let _ = Checker.check_module processed_ast tbl smtEnv session in

    Stdio.print_endline "Verification successful.\n"


  | _ -> raise (Generic_Error "SymbolTbl should be empty")

let parse_program filename =
  let resource_algebra_file = "lib/library/resource_algebra.rav" in
  let inx_ra = Stdio.In_channel.create resource_algebra_file in
  let lexbuf_lib = Lexing.from_channel inx_ra in
  Lexer.set_file_name lexbuf_lib resource_algebra_file;

  (* --- *)
  let tbl, smtEnv, session = parse_lib lexbuf_lib in
  Smt_solver.write_comment session "End of Library";
  Smt_solver.write_comment session "";
  Smt_solver.write_comment session "";

  (* Keep above section to process Library file; keep below section to not process Library file. *)

  (* let tbl = Process_ast.SymbolTbl.push [] in
  let smtEnv = Smt_solver.SmtEnv.push ([], []) in
  let session = Smt_solver.init () in *)
  (* --- *)

  Smt_solver.write_comment session "---- Starting Program ----";

  let inx = Stdio.In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  Lexer.set_file_name lexbuf filename;

  let _ =
    try parse_and_print lexbuf tbl smtEnv session
    with Parser.Error ->
      Stdio.In_channel.close inx;
      let err_pos = lexbuf.lex_curr_p in
      Error.syntax_error (Loc.make err_pos err_pos) None
  in
  Stdio.In_channel.close inx

let () =
  (* Backtrace.Exn.set_recording true; *)
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
