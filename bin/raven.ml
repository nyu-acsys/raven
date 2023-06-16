open Base
open Util
open Frontend
open Backend

(** Parse a single compilation unit from file [file_name] as a module named [top_level_md_ident]. *)
let parse_cu top_level_md_ident file_name =
  let inchan = Stdio.In_channel.create file_name in
  let lexbuf = Lexing.from_channel inchan in
  let _ = Lexer.set_file_name lexbuf file_name in
  let md =
    try Parser.main Lexer.token lexbuf
    with Parser.Error ->
      Stdio.In_channel.close inchan;
      let err_pos = lexbuf.lex_curr_p in
      Error.syntax_error (Loc.make err_pos err_pos) None
  in
  Stdio.In_channel.close inchan;
  Ast.Module.set_name md top_level_md_ident

(** Parse and check compilation unit from file [file_name] as a module named [top_level_md_ident]. *)
let parse_and_check_cu ?(tbl=None) smtEnv session top_level_md_ident file_name =
  Logs.info (fun m -> m "Processing file %s." file_name);
  let md = parse_cu top_level_md_ident file_name in
  let processed_md, tbl = Typing.process_module ?tbl md in
  match tbl with
  | [ _ ; _ ] | [ _ ] -> 
    Logs.debug (fun m -> m "SymbolTbl: \n%s\n" (SymbolTbl.to_string tbl));
    (*Logs.debug (fun m -> m !"%{Ast.Module}" processed_md);*)
    Logs.info (fun m -> m "Front-end processing successful.");

    let session, smtEnv = Checker.check_module processed_md tbl smtEnv session in
    Logs.info (fun m -> m "Verification of file %s successful." file_name);
    session, smtEnv, tbl

  | _ -> failwith "SymbolTbl should be empty"

(** Parse and check all compilation units in files [file_names] *)
let parse_and_check_all file_names =
  (* Start backend solver session *)
  let session, smtEnv = Checker.start_session () in
  
  (* Parse and check standard library *)
  let lib_file = "lib/library/resource_algebra.rav" in
  let smtEnv, session, tbl = parse_and_check_cu smtEnv session (Ast.Ident.make "Lib" 0) lib_file in
  
  (* Parse and check actual input program *)
  let _ =
    List.fold_left file_names ~init:(smtEnv, session, tbl)
      ~f:(fun (smtEnv, session, tbl) file_name ->
          parse_and_check_cu ~tbl:(Some tbl) smtEnv session (Ast.Ident.make "$Program" 0) file_name)
  in

  Checker.stop_session session;
  
  Logs.app (fun m -> m "Verification successful.")

(** Command line interface *)

open Cmdliner

let setup_config_cmd style_renderer level =
  (* Set up logger *)
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  let pp_header ~pp_h ppf (l, h) = match l with
      | Logs.App ->
        begin match h with
          | None -> ()
          | Some h -> Fmt.pf ppf "[%a] " Fmt.(styled Logs_fmt.app_style string) h
        end
      | Logs.Error ->
        pp_h ppf Logs_fmt.err_style (match h with None -> "Error" | Some h -> h)
      | Logs.Warning ->
        pp_h ppf Logs_fmt.warn_style (match h with None -> "Warning" | Some h -> h)
      | Logs.Info ->
        pp_h ppf Logs_fmt.info_style (match h with None -> "Info" | Some h -> h)
      | Logs.Debug ->
        pp_h ppf Logs_fmt.debug_style (match h with None -> "Debug" | Some h -> h)
  in
  let pp_h ppf style h = Fmt.pf ppf "[%a] " Fmt.(styled style string) h in
  Logs.set_reporter (Logs_fmt.reporter ~pp_header:(pp_header ~pp_h) ());
  ()

let setup_config =
  Term.(const setup_config_cmd $ Fmt_cli.style_renderer () $ Logs_cli.level ())

let input_file =
  let doc = "Input file." in
  Arg.(value & (pos_all non_dir_file []) & info [] ~docv:"INPUT" ~doc)

let greeting = "Raven version " ^ Config.version

let main () input_files = 
  Logs.app (fun m -> m "%s" greeting);
  try `Ok (parse_and_check_all input_files) with
  | Sys_error s | Failure s | Invalid_argument s ->
      Logs.err (fun m -> m "%s" s);
      Logs.debug (fun m -> m "\n---------\n%s" @@ Backtrace.to_string (Backtrace.Exn.most_recent ()));
      Stdlib.exit 1 (* `Error (false, s) <- duplicates error output *)
  | Error.Msg e ->
      Logs.err (fun m -> m !"%{Error}" e);
      Logs.debug (fun m -> m "\n---------\n%s" @@ Backtrace.to_string (Backtrace.Exn.most_recent ()));
      Stdlib.exit 1 (* duplicates error output: `Error (false, "") *)


let main_cmd =
  let info = Cmd.info "raven" ~version:Config.version in
  Cmd.v info Term.(ret (const main $ setup_config $ input_file))

let () = Stdlib.exit (Cmd.eval main_cmd)
