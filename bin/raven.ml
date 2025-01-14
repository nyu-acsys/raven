open Base
open Util
open Ast
open Frontend

type config = {
  no_library: bool;
  typecheck_only: bool;
  lsp_mode: bool;
  base_dir: string;
  prog_stats: bool;
  smt_timeout: int;
  smt_diagnostics: bool;
}

let stream_of_file file_name =
  let inchan = Stdio.In_channel.create file_name in
  let lexbuf = Lexing.from_channel inchan in
  let _ = Lexer.set_file_name lexbuf file_name in
  (inchan, lexbuf)

let normalizeFilename base_dir file_name =
  let fullname =
    if Stdlib.Filename.is_relative file_name then
      base_dir ^ Stdlib.Filename.dir_sep ^ file_name
    else file_name
  in
  let sep = Str.regexp_string Stdlib.Filename.dir_sep in
  let parts = Str.split_delim sep fullname in
  let remaining =
    List.fold_left
      ~f:(fun acc -> function
        | "" when not (List.is_empty acc) -> acc
        | "." -> acc
        | ".." -> List.tl_exn acc
        | x -> x :: acc)
      ~init:[] parts
  in
  String.concat ~sep:Stdlib.Filename.dir_sep (List.rev remaining)

(** Parse a single compilation unit from file [file_name] as a module named [top_level_md_ident]. *)
let parse_cu top_level_md_ident lexbuf =
  let incls, md =
    try Parser.main Lexer.token lexbuf
    with Parser.Error ->
      let err_pos = lexbuf.lex_curr_p in
      Error.syntax_error (Loc.make err_pos err_pos) "Parse error"
  in

  (incls, Ast.Module.set_name md top_level_md_ident)

let check_cu config tbl smt_env md front_end_out_chan =
  let tbl = SymbolTbl.add_symbol (ModDef md) tbl in
  let tbl, processed_md = Typing.process_module ~tbl md in
  Logs.debug (fun m -> m !"%a" Ast.Module.pr processed_md);
  Logs.info (fun m -> m "Type-checking successful.");

  if config.typecheck_only then (smt_env, tbl) else
  
  if config.prog_stats 
    && not String.((Ident.to_string md.mod_decl.mod_decl_name) = "Library") 
  then 
    let _ = 
      Logs.debug (fun m -> m "Computing stats of module: %a" Ident.pr processed_md.mod_decl.mod_decl_name) 
    in
    let prog_stats = Rewrites.compute_stats tbl processed_md in

    Logs.app (fun m -> m
      "\nPROGRAM STATISTICS: \n%a"
      Rewrites.ProgStats.pr prog_stats
    );
    Stdlib.exit 0
  else begin

  let tbl, processed_md = Rewrites.process_module ~tbl processed_md in

  Logs.debug (fun m ->
      m "SymbolTbl Symbols: \n%a\n"
        (Util.Print.pr_list_comma (fun ppf (k, v) ->
             Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k
               Module.pr_symbol v))
        (Map.to_alist
           (Map.filter_keys tbl.tbl_symbols ~f:(fun k ->
                Poly.(QualIdent.to_string k = "$Program.pr")))));

  Logs.debug (fun m -> m !"%a" Ast.Module.pr processed_md);
  Logs.info (fun m -> m "Front-end processing successful.");

  Stdlib.Format.fprintf
    (Stdlib.Format.formatter_of_out_channel front_end_out_chan)
    "%a\n" Ast.Module.pr processed_md;

  let smt_env = Backend.Checker.check_module processed_md tbl smt_env in
  (smt_env, tbl)
  end

(** Parse and check compilation unit from file [file_name] as a module named [top_level_md_ident]. *)
let parse_and_check_cu ?(tbl = SymbolTbl.create ()) smt_env top_level_md_ident
    lexbuf front_end_out_chan =
  (* let root_ident = SymbolTbl.root_ident tbl |> Ast.QualIdent.to_ident in *)
  let _, md = parse_cu top_level_md_ident lexbuf in
  let tbl = SymbolTbl.add_symbol (ModDef md) tbl in
  let tbl, processed_md = Typing.process_module ~tbl md in
  Logs.debug (fun m -> m !"%a" Ast.Module.pr processed_md);
  Logs.info (fun m -> m "Type-checking successful.");

  let tbl, processed_md = Rewrites.process_module ~tbl processed_md in

  Logs.debug (fun m ->
      m "SymbolTbl Symbols: \n%a\n"
        (Util.Print.pr_list_comma (fun ppf (k, v) ->
             Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k
               Module.pr_symbol v))
        (Map.to_alist
           (Map.filter_keys tbl.tbl_symbols ~f:(fun k ->
                Poly.(QualIdent.to_string k = "$Program.pr")))));

  Logs.debug (fun m -> m !"%a" Ast.Module.pr processed_md);
  Logs.info (fun m -> m "Front-end processing successful.");

  Stdlib.Format.fprintf
    (Stdlib.Format.formatter_of_out_channel front_end_out_chan)
    "%a\n" Ast.Module.pr processed_md;

  let smt_env = Backend.Checker.check_module processed_md tbl smt_env in
  (smt_env, tbl)

(** Parse and check all compilation units in files [file_names] *)
let parse_and_check_all config file_names =
  (* Start backend solver session *)
  let smt_env = Backend.Smt_solver.init config.smt_diagnostics config.smt_timeout in

  let front_end_processed_output_log = "front_end_processed_output.log" in
  let front_end_out_chan =
    Stdio.Out_channel.create front_end_processed_output_log
  in

  (* Parse and check standard library *)
  let tbl = SymbolTbl.create () in
  let smt_env, tbl =
    if config.no_library then (smt_env, tbl)
    else
      let lib_prog =
        List.fold_right Library.sources ~init:empty_prog
        ~f:(fun (lib_file_name, lib_source) lib_prog ->
            let lib_source_lexbuf =
              Lexing.from_string lib_source
            in
            let _ =
              Lexer.set_file_name lib_source_lexbuf lib_file_name
            in
            let _includes, md = parse_cu Predefs.lib_ident lib_source_lexbuf in
            let md = Ast.Module.set_free md in
            merge_prog md lib_prog)
      in
          (*  parse_and_check_cu ~tbl smt_env Predefs.lib_ident resource_algebra_lexbuf
              front_end_out_chan*)
      check_cu config tbl smt_env lib_prog front_end_out_chan
  in
  
  (* Parse and check actual input program *)
  let rec parse_prog parsed to_parse prog =
    match to_parse with
    | [] -> prog
    | (file_dir, file_name, is_free) :: to_parse1 ->
        if not (Set.mem parsed file_name) then (
          Logs.debug (fun m -> m "raven.parse_prog: Parsing file %s." file_name);
          let inchan, lexbuf = stream_of_file file_name in
          let includes, md = parse_cu Predefs.prog_ident lexbuf in

          Stdio.In_channel.close inchan;

          let md =
            if is_free then
              let md = Ast.Module.set_free md in
              md
            else md
          in

          let parsed = Set.add parsed file_name in

          let to_parse2 =
            List.fold_left includes ~init:to_parse1 ~f:(fun acc incl ->
                let incl = normalizeFilename file_dir incl in
                let dir = Stdlib.Filename.dirname incl in
                acc @ [ (dir, incl, true) ])
          in
          parse_prog parsed to_parse2 (merge_prog md prog))
        else (
          Logs.debug (fun m ->
              m "raven.parse_prog: Skipping file %s." file_name);
          parse_prog parsed to_parse1 prog)
  in

  let md =
    parse_prog
      (Set.empty (module String))
      (List.rev_map ~f:(fun file_name ->
             let norm_dir = normalizeFilename (Unix.getcwd ()) config.base_dir in
             let norm_file_name = normalizeFilename norm_dir file_name in
             let file_dir  =
               if String.(config.base_dir <> "") then norm_dir
               else Stdlib.Filename.dirname norm_file_name
             in
             (file_dir, file_name, false)) file_names)
      empty_prog
  in

  begin
  let _ = check_cu config tbl smt_env md front_end_out_chan in

  (* Check all files *)

  (* let _ =
       List.fold_left file_names ~init:(smt_env, tbl)
         ~f:(fun (smt_env, tbl) file_name ->
           let inchan, lexbuf = stream_of_file file_name in

           Logs.info (fun m -> m "Processing file %s." file_name);
           let smt_env, tbl = parse_and_check_cu ~tbl smt_env Predefs.prog_ident lexbuf front_end_out_chan in

           Stdio.In_channel.close inchan;
           Logs.info (fun m -> m "Verification of file %s successful." file_name);

           smt_env, tbl
           )
     in *)

  (*Checker.stop_session session;*)
  Logs.app (fun m -> m "Verification successful.")
  end

(** Command line interface *)

open Cmdliner

let setup_config_cmd style_renderer level =
  (* Set up logger *)
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  let pp_header ~pp_h ppf (l, h) =
    match l with
    | Logs.App -> (
        match h with
        | None -> ()
        | Some h -> Fmt.pf ppf "[%a] " Fmt.(styled Logs_fmt.app_style string) h)
    | Logs.Error ->
        pp_h ppf Logs_fmt.err_style
          (match h with None -> "Error" | Some h -> h)
    | Logs.Warning ->
        pp_h ppf Logs_fmt.warn_style
          (match h with None -> "Warning" | Some h -> h)
    | Logs.Info ->
        pp_h ppf Logs_fmt.info_style
          (match h with None -> "Info" | Some h -> h)
    | Logs.Debug ->
        pp_h ppf Logs_fmt.debug_style
          (match h with None -> "Debug" | Some h -> h)
  in
  let pp_h ppf style h = Fmt.pf ppf "[%a] " Fmt.(styled style string) h in
  Logs.set_reporter (Logs_fmt.reporter ~pp_header:(pp_header ~pp_h) ());
  ()

let setup_config =
  Term.(const setup_config_cmd $ Fmt_cli.style_renderer () $ Logs_cli.level ())

let input_file =
  let doc = "Input file." in
  Arg.(value & pos_all non_dir_file [] & info [] ~docv:"INPUT" ~doc)

let no_greeting =
  let doc = "Suppress greeting." in
  Arg.(value & flag & info [ "shh" ] ~doc)

let no_library =
  let doc = "Skip standard library." in
  Arg.(value & flag & info [ "nostdlib" ] ~doc)

let prog_stats =
  let doc = "Output only program stats: concrete instruction steps, ghost instruction steps, and number of specification formulae" in
  Arg.(value & flag & info [ "stats" ] ~doc)

let smt_diagnostics =
  let doc = "Let Z3 produce diagostic output." in
  Arg.(value & flag & info [ "smt-info" ] ~doc)

let typecheck_only =
  let doc = "Only type-check input program but do not verify it." in
  Arg.(value & flag & info [ "typeonly" ] ~doc)

let lsp_mode =
  let doc = "Format error messages for LSP integration." in
  Arg.(value & flag & info [ "lsp-mode" ] ~doc)

let base_dir =
  let doc = "Base directory for resolving include directives. Default: current working directory." in
  Arg.(value & opt string "" & info [ "base-dir"] ~doc)

let smt_timeout =
  let doc = "Timeout for SMT solver in ms." in 
  Arg.(value & opt int 10000 & info [ "smt-timeout" ] ~doc)

let greeting = "Raven version " ^ Config.version

let print_errors config errs =
  if config.lsp_mode then begin
    Stdlib.print_endline (Error.errors_to_lsp_string errs);
    Stdlib.exit 0
  end
  else begin
    List.iter errs ~f:(fun e -> Logs.err (fun m -> m !"%{Error}" e));
    Logs.debug (fun m ->
        m "\n---------\n%s"
        @@ Backtrace.to_string (Backtrace.Exn.most_recent ()));
    Stdlib.exit 1 (* duplicates error output: `Error (false, "") *)
  end

let main () input_files no_greeting no_library typecheck_only lsp_mode base_dir prog_stats smt_timeout smt_diagnostics =
  if not no_greeting then Logs.app (fun m -> m "%s" greeting) else ();
  let config = {
    no_library;
    typecheck_only;
    lsp_mode;
    prog_stats;
    base_dir;
    smt_timeout;
    smt_diagnostics;
  }
  in
  try `Ok (parse_and_check_all config input_files) with
  | Sys_error s | Failure s | Invalid_argument s ->
    print_errors config [Internal, Loc.dummy, s]
  | Error.Msg es ->
    print_errors config es
      
let main_cmd =
  let info = Cmd.info "raven" ~version:Config.version in
  Cmd.v info
    Term.(
      ret (const main $ setup_config $ input_file $ no_greeting $ no_library $ typecheck_only $ lsp_mode $ base_dir $ prog_stats $ smt_timeout $ smt_diagnostics))

let () = Stdlib.exit (Cmd.eval main_cmd)
