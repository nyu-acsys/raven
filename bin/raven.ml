open Base
open Util
open Ast
open Frontend
(*open Backend*)

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
let parse_and_check_cu ?(tbl=SymbolTbl.create ()) smtEnv top_level_md_ident file_name front_end_out_chan =
  Logs.info (fun m -> m "Processing file %s." file_name);
  (* let root_ident = SymbolTbl.root_ident tbl |> Ast.QualIdent.to_ident in *)
  let md = parse_cu top_level_md_ident file_name in
  let tbl = SymbolTbl.add_symbol (ModDef md) tbl in
  let tbl, processed_md = Typing.process_module ~tbl md in
  Logs.debug (fun m -> m !"%a" Ast.Module.pr processed_md);
  Logs.info (fun m -> m "Type-checking successful.");

  let tbl, processed_md = Rewrites.process_module (*Rewrites.Rewriting.process_module*) ~tbl processed_md in

  Logs.debug (fun m -> m "SymbolTbl Symbols: \n%a\n" (Util.Print.pr_list_comma (fun ppf (k,v) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k Module.pr_symbol v)) (Map.to_alist (Map.filter_keys tbl.tbl_symbols ~f:(fun k -> Poly.((QualIdent.to_string k) = "$Program.pr")))));

  (*Logs.debug (fun m -> m "SymbolTbl: \n%s\n" (SymbolTbl.to_string tbl));*)
  Logs.debug (fun m -> m !"%a" Ast.Module.pr processed_md);
  Logs.info (fun m -> m "Front-end processing successful.");

  Stdlib.Format.fprintf (Stdlib.Format.formatter_of_out_channel front_end_out_chan) "%a\n" Ast.Module.pr processed_md;

  let smtEnv = Backend.Checker.check_module processed_md tbl smtEnv in
  Logs.info (fun m -> m "Verification of file %s successful." file_name);
  smtEnv, tbl


(** Parse and check all compilation units in files [file_names] *)
let parse_and_check_all file_names =
  (* Start backend solver session *)
  let smtEnv = Backend.Smt_solver_new.init () in

  let front_end_processed_output_log = "front_end_processed_output.log" in
  let front_end_out_chan = Stdio.Out_channel.create front_end_processed_output_log in
  
  (* Parse and check standard library *)
  let lib_file = Stdlib.Filename.dirname (Sys.get_argv ()).(0) ^ "/../lib/library/resource_algebra.rav" in
  let tbl = SymbolTbl.create () in
  let smtEnv, tbl = parse_and_check_cu ~tbl smtEnv Predefs.lib_ident lib_file front_end_out_chan in
  
  (* Parse and check actual input program *)
  let _ =
    List.fold_left file_names ~init:(smtEnv, tbl)
      ~f:(fun (smtEnv, tbl) file_name ->
          parse_and_check_cu ~tbl smtEnv Predefs.prog_ident file_name front_end_out_chan)
  in

  (*Checker.stop_session session;*)

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

let no_greeting = 
  let doc = "Suppress greeting." in
  Arg.(value & flag & info ["shh"] ~doc)

let greeting = "Raven version " ^ Config.version

let main () input_files no_greeting = 
  (if not no_greeting then
    Logs.app (fun m -> m "%s" greeting)
  else
    ());
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
  Cmd.v info Term.(ret (const main $ setup_config $ input_file $ no_greeting))

let () = Stdlib.exit (Cmd.eval main_cmd)
