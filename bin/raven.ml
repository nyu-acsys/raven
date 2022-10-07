open Base
open Util
open Frontend
open Error

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
  let disambiguated_ast, tbl = Resolve_namespaces.start_disambiguate s in
  match tbl with
  | [ _ ] ->
      if type_checking_enabled then (
        Ast.print_debug ("\027[32m" ^ "STARTING TYPE-CHECK\n" ^ "\027[0m");
        let type_checked_ast, tbl =
          Type_checker.start_type_check disambiguated_ast
        in
        match tbl with
        | [ _ ] ->
            Ast.Module.print_verbose Stdio.stdout type_checked_ast;
            Stdio.print_endline ""
        | _ -> raise (Failure "SymbolTbl should be empty: 2"))
      else Ast.Module.print_verbose Stdio.stdout disambiguated_ast;
      Stdio.print_endline ""
  | _ -> raise (Failure "SymbolTbl should be empty: 1")

(* Ast.Module.print Stdio.stdout s;
   Stdio.print_endline "" *)

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
      Stdlib.exit 1
  | Error.Msg _ as e ->
      Stdio.prerr_endline (Error.to_string e);
      Stdlib.exit 1
