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
  log_level: Logs.level option;
  strict: bool;
}

let include_map = Hashtbl.create (module String)


let stream_of_file file_name =
  let inchan = Stdio.In_channel.create file_name in
  let lexbuf = Lexing.from_channel inchan in
  let _ = Lexer.set_file_name lexbuf file_name in
  (inchan, lexbuf)

(* `include` paths in .rav source are always written with forward slashes
   (portable, editor-agnostic convention -- see e.g. test/concurrent/templates),
   regardless of which OS raven runs on. Splitting only on Filename.dir_sep -- "\\"
   on Windows -- would leave a "./"-prefixed include like "./ccm.rav" un-split, so it
   normalizes to a different string than a same-file include written as "ccm.rav"
   elsewhere; the two spellings then dedupe as different files and get declared
   twice. Split on either separator so both spellings always normalize the same way,
   and always rejoin with "/" so the result is one canonical, platform-independent
   string throughout (used as-is both as a file path -- Windows accepts "/" same as
   "\\" -- and in diagnostics, where dune's cram tests expect forward slashes). *)
let normalizeFilename base_dir file_name =
  let fullname =
    if Stdlib.Filename.is_relative file_name then
      base_dir ^ Stdlib.Filename.dir_sep ^ file_name
    else file_name
  in
  let sep = Str.regexp "[/\\\\]" in
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
  String.concat ~sep:"/" (List.rev remaining)

(** Parse a single compilation unit from file [file_name] as a module named [top_level_md_ident]. *)
let parse_cu file_dir top_level_md_ident lexbuf =
  let incls, md =
    try Parser.main (Lexer.make_token ()) lexbuf
    with Parser.Error ->
      let err_pos = lexbuf.lex_curr_p in
      let tok = Lexing.lexeme lexbuf in
      let msg =
        if String.is_empty tok then "Unexpected end of file"
        else Printf.sprintf "Unexpected token '%s'" tok
      in
      Error.syntax_error (Loc.make err_pos err_pos) msg
  in
  let incls = List.map incls ~f:(fun (incl, loc) ->
      let incl = normalizeFilename file_dir incl in
      let dir = Stdlib.Filename.dirname incl in
      Logs.info (fun m -> m "%s" incl);
      ignore (Hashtbl.add include_map ~key:incl ~data:loc);
      (dir, incl, true))
  in
  (incls, Ast.Module.set_name md top_level_md_ident)

(** Under `--strict`, warns about every explicit `free` in [md] (recursing into nested
    modules). Must run before [Ast.Module.set_free] force-marks a whole file free (e.g.
    for stdlib/includes below) -- once applied, that override is indistinguishable from
    a literal `free` written by the user. *)
let rec warn_free_usage (md : Ast.Module.t) =
  List.iter md.mod_def ~f:(function
    | Ast.Module.SymbolDef symbol ->
      if Ast.Symbol.is_free symbol then
        Logs.warn (fun m -> m "%s%s"
          (Loc.to_string (Ast.Symbol.to_loc symbol))
          (Printf.sprintf
             !"%s %{Ident} is declared `free`; its contract will be assumed for verification purposes, not checked"
             (Ast.Symbol.kind symbol) (Ast.Symbol.to_name symbol)));
      (match symbol with
       | Ast.Module.ModDef mod_def -> warn_free_usage mod_def
       | _ -> ())
    | Ast.Module.Import _ -> ())

(** Type-checks and front-end-processes (rewrites) a single compilation unit. This is
    kept separate from the actual backend/SMT checking ([backend_check_cu] below) so that
    the full set of tuple sorts a program needs (see [Backend.TupleArities]) can be
    computed from the fully elaborated symbol table -- of both the library and the main
    program -- before any backend checking (and hence any tuple-sort declaration) begins.
    Returns [None] in place of the processed module when there is nothing to backend-check
    (`--typeonly`); the `--stats` short-circuit below exits the process directly, as
    before. *)
let elaborate_cu ~ext_hooks config tbl md front_end_out_chan =
  let cli_config : Rewriter.cli_config = { cli_strict = config.strict } in
  let printers = Rewriter.printers_of_ext_hooks ext_hooks in
  let tbl = SymbolTbl.add_symbol (ModDef md) tbl in
  let tbl, processed_md = Typing.process_module ~tbl ~ext_hooks ~cli_config md in
  Logs.debug (fun m -> m "%a" printers.pr_module processed_md);
  Logs.info (fun m -> m "Type-checking successful.");

  if config.typecheck_only then (tbl, None) else

  if config.prog_stats
    && not String.((Ident.to_string md.mod_decl.mod_decl_name) = "Library")
  then
    let _ =
      Logs.debug (fun m -> m "Computing stats of module: %a" Ident.pr processed_md.mod_decl.mod_decl_name)
    in
    let prog_stats = Rewrites.compute_stats ~ext_hooks tbl processed_md in

    Logs.app (fun m -> m
      "\nPROGRAM STATISTICS: \n%a"
      Rewrites.ProgStats.pr prog_stats
    );
    Stdlib.exit 0
  else begin

  let tbl, processed_md = Rewrites.process_module ~tbl ~ext_hooks ~cli_config processed_md in

  (* Logs.debug (fun m ->
      m "SymbolTbl Symbols: \n%a\n"
        (Util.Print.pr_list_comma (fun ppf (k, v) ->
             Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k
               Module.pr_symbol v))
        (Map.to_alist
           (Map.filter_keys tbl.tbl_symbols ~f:(fun k ->
                Poly.(QualIdent.to_string k = "$Program.pr"))))); *)

  Logs.debug (fun m -> m "%a" printers.pr_module processed_md);
  Logs.info (fun m -> m "Front-end processing successful.");

  Stdlib.Format.fprintf
    (Stdlib.Format.formatter_of_out_channel front_end_out_chan)
    "%a\n" printers.pr_module processed_md;

  (tbl, Some processed_md)
  end

(** Runs backend/SMT checking for a single already-elaborated compilation unit. *)
let backend_check_cu tbl smt_env processed_md =
  Backend.Checker.check_module processed_md tbl smt_env


(** Parse and check all compilation units in files [file_names] *)
let parse_and_check_all ~ext_hooks ~lib_sources config file_names =
  (* Locations inside extension library sources (e.g. well_founded_order.rav) are
     virtual -- there's no real file on disk for Loc.context to fall back to reading.
     Register them so it can find the text the same way it already does for the core
     standard library ([Library.sources]). *)
  Loc.register_sources lib_sources;

  (* Start backend solver session *)
  
  (* Variable which controls whether the 
    - `front_end_processed_output.log` 
    - `log.smt2`
    files are created. 
    At present create them only when in Debug mode and also not in lsp_mode.
   *)
  let external_logging = 
    match config.log_level with
    | Some Logs.Debug ->
      if config.lsp_mode then false else
        true
    | _ -> false
  in

  let smt_env = Backend.Smt_solver.init ~logging:external_logging config.smt_diagnostics config.smt_timeout in
  Stdlib.Fun.protect ~finally:(fun () -> Backend.Smt_solver.stop smt_env) @@ fun () ->

  let front_end_processed_output_log = "front_end_processed_output.log" in
  let front_end_out_chan =
    if external_logging then
      Stdio.Out_channel.create front_end_processed_output_log
    else 
      Util.Channel.null_channel ()
  in

  (* Parse and check standard library *)
  let tbl = SymbolTbl.create () in
  let tbl, lib_processed_md =
    if config.no_library then (tbl, None)
    else
      let lib_prog =
        List.fold_right (Library.sources @ lib_sources) ~init:empty_prog
        ~f:(fun (lib_file_name, lib_source) lib_prog ->
            let lib_source_lexbuf =
              Lexing.from_string lib_source
            in
            let _ =
              Lexer.set_file_name lib_source_lexbuf lib_file_name
            in
            let _includes, md = parse_cu (Stdlib.Filename.dirname lib_file_name) Predefs.lib_ident lib_source_lexbuf in
            (* [set_unit_free], not [set_free]: the standard library is trusted by the
               compiler so it isn't re-verified for every program, which is exactly what
               [MachineFree] means -- as opposed to [UserFree], a `free` the user wrote.
               The two must stay distinguishable: a member inherited from here into a
               user module still owes a definition and a proof, whereas one inherited
               from a user's own `free` declaration does not (see [Typing.merge_defs]). *)
            let md = Ast.Module.set_unit_free md in
            merge_prog md lib_prog)
      in
      elaborate_cu ~ext_hooks config tbl lib_prog front_end_out_chan
  in
  
  (* Parse and check actual input program *)
  let rec parse_prog parsed to_parse prog =
    match to_parse with
    | [] -> prog
    | (file_dir, file_name, is_free) :: to_parse1 ->
        if not (Set.mem parsed file_name) then (
          Logs.debug (fun m -> m "raven.parse_prog: Parsing file %s." file_name);
          let inchan, lexbuf =
            try stream_of_file file_name
            with Sys_error _ ->
              let loc = Hashtbl.find include_map file_name |> Option.value ~default:Loc.dummy in
              Error.error loc (Printf.sprintf "Cannot find file '%s' (referenced by an include)" file_name)
          in
          let includes, md = parse_cu file_dir Predefs.prog_ident lexbuf in

          if config.strict then warn_free_usage md;

          Stdio.In_channel.close inchan;

          let md =
            (* [is_free] here is set unconditionally for every `include`d file (see
               [parse_cu]) -- there is no `free include` syntax -- so this is the
               compiler's decision, not the user's, and uses [set_unit_free] for the
               same reason the standard library above does. Marking it [UserFree]
               instead used to let a module implementing an interface from an included
               file skip both halves of the conformance check. *)
            if is_free then Ast.Module.set_unit_free md else md
          in

          let parsed = Set.add parsed file_name in

          let to_parse2 = to_parse1 @ includes in
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

  let tbl, prog_processed_md = elaborate_cu ~ext_hooks config tbl md front_end_out_chan in

  begin
  (* Logs.debug (fun m -> m "Final symboltbl.tbl_symbols: %a" (Util.Print.pr_list_comma QualIdent.pr) (Map.keys tbl.tbl_symbols)); *)
  let processed_mds = List.filter_map [ lib_processed_md; prog_processed_md ] ~f:Fn.id in

  (match processed_mds with
   | [] -> (* `--typeonly`: nothing left to backend-check *) ()
   | _ ->
     (* Only now -- once both the library and the main program have been fully
        elaborated -- do we know every tuple sort ([$tuple_n]) the program actually
        needs (see Backend.TupleArities), so this is the earliest point at which we
        can declare them. *)
     let arities = Backend.TupleArities.of_symbols (Map.data tbl.tbl_symbols) in
     let smt_env = Backend.Smt_solver.declare_tuple_sorts smt_env arities in
     let (_ : Backend.Smt_solver.smt_env) =
       List.fold processed_mds ~init:smt_env ~f:(backend_check_cu tbl)
     in
     ());

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

let extension_mode =
  let doc = "Extension mode: default, eris, or prophecy." in
  let supported_exts = List.map ~f:(fun (e, _) -> (e, e)) Ext.ext_map in
  Arg.(value & opt (enum supported_exts) "default" & info [ "extension" ] ~doc)

let strict =
  let doc = "Warn about recursive lemmas/functions and loops in lemmas missing \
             `decreases` clauses, and about explicit user use of `free`." in
  Arg.(value & flag & info [ "strict" ] ~doc)

let greeting = "Raven version " ^ Config.version

let print_errors config errs =
  let rec remap ((kind, loc, msg) as err) =
    match Hashtbl.find include_map (Loc.file_name loc) with
    | Some loc1 -> remap (kind, loc1, "originates in included file")
    | None -> err
  in
  if config.lsp_mode then begin
    let errs = List.map errs ~f:remap in
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

let main () input_files no_greeting no_library typecheck_only lsp_mode base_dir prog_stats smt_timeout smt_diagnostics extension_mode strict =
  if not no_greeting then Logs.app (fun m -> m "%s" greeting) else ();
  let config = {
    no_library;
    typecheck_only;
    lsp_mode;
    prog_stats;
    base_dir;
    smt_timeout;
    smt_diagnostics;
    log_level = Logs.level ();
    strict;
  }
  in
  (* [EXT] Resolve which extension is activated for this run and build the hooks the
     rest of the pipeline dispatches through -- see lib/ext/ext.ml and
     Ast.Rewriter.ext_hooks. *)
  let (module ChosenExt) =
    Ext.module_map (List.Assoc.find_exn ~equal:String.(=) Ext.ext_map extension_mode)
  in
  let ext_hooks = Ext.to_ext_hooks (module ChosenExt : ExtApi.Ext) in
  try `Ok (parse_and_check_all ~ext_hooks ~lib_sources:ChosenExt.lib_sources config input_files) with
  | Unix.Unix_error (err, _, prog) ->
    let msg =
      Printf.sprintf
        "Could not start '%s' (%s). Raven requires Z3 (>= 4.13.0) to be installed and on your PATH."
        prog (Unix.error_message err)
    in
    print_errors config [ (Generic, Loc.dummy, msg) ]
  | Sys_error _ | Failure _ | Invalid_argument _ | Assert_failure _ as exn ->
    let msg = String.map ~f:(function '"' -> '\'' | c -> c) (Exn.to_string exn) in
    let pos = match input_files with
      | file :: _ ->
        Loc.make Lexing.{ pos_fname = file; pos_bol = 0; pos_cnum = 0; pos_lnum = 1 }
          Lexing.{ pos_fname = file; pos_bol = 0; pos_cnum = 0; pos_lnum = 1 }
      | _ -> Loc.dummy
    in
    print_errors config [Internal, pos, msg]
  | Error.Msg es ->
    print_errors config es

let main_cmd =
  let info = Cmd.info "raven" ~version:Config.version in
  Cmd.v info
    Term.(
      ret (const main $ setup_config $ input_file $ no_greeting $ no_library $ typecheck_only $ lsp_mode $ base_dir $ prog_stats $ smt_timeout $ smt_diagnostics $ extension_mode $ strict))

let () = Stdlib.exit (Cmd.eval main_cmd)
