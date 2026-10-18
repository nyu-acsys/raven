open Base
open Util
open Ast
open Frontend

type config = {
  no_library : bool;
  typecheck_only : bool;
  lsp_mode : bool;
  lsp_annotations : bool;
  base_dir : string;
  prog_stats : bool;
  smt_timeout : int;
  smt_diagnostics : bool;
  max_errors : int option;  (** As given on the command line, if at all. *)
  log_level : Logs.level option;
  strict : bool;
  only : string option;
      (** The member, module or named assertion to verify, if not all. *)
  counterexamples : bool;
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

(** Parse a single compilation unit from file [file_name] as a module named
    [top_level_md_ident]. *)
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
  let incls =
    List.map incls ~f:(fun (incl, loc) ->
        let incl = normalizeFilename file_dir incl in
        let dir = Stdlib.Filename.dirname incl in
        Logs.info (fun m -> m "%s" incl);
        ignore (Hashtbl.add include_map ~key:incl ~data:loc);
        (dir, incl, true))
  in
  (incls, Ast.Module.set_name md top_level_md_ident)

(** Under `--strict`, warns about every explicit `free` in [md] (recursing into nested
    modules). Must run before [Ast.Module.set_free] force-marks a whole file free (e.g.
    for stdlib/includes below) -- once applied, that override is indistinguishable from a
    literal `free` written by the user. *)
let rec warn_free_usage ~diagnostics (md : Ast.Module.t) =
  List.iter md.mod_def ~f:(function
    | Ast.Module.SymbolDef symbol -> (
        if Ast.Symbol.is_free symbol then
          Diagnostics.warning diagnostics (Ast.Symbol.to_loc symbol)
            (Printf.sprintf
               !"%s %{Ident} is declared `free`; its contract will be assumed for \
                 verification purposes, not checked"
               (Ast.Symbol.kind symbol) (Ast.Symbol.to_name symbol));
        match symbol with
        | Ast.Module.ModDef mod_def -> warn_free_usage ~diagnostics mod_def
        | _ -> ())
    | Ast.Module.Import _ -> ())

(** The limit on the errors a run reports, [None] for none. Without `--max-errors`, it is
    20, but `--lsp-mode` has none, since an editor can show every error. *)
let max_errors_of config =
  match config.max_errors with
  | Some limit -> if limit <= 0 then None else Some limit
  | None -> if config.lsp_mode then None else Some 20

let cli_config_of config : Rewriter.cli_config = { cli_strict = config.strict }

(** Type-checks a single compilation unit.

    Kept separate from [rewrite_cu] so that *every* unit can be type-checked before any is
    rewritten. Type-checking a unit against an already-rewritten one does not work in
    general: the rewrite phase replaces a field's declared type with its resource algebra
    and generates the artifacts that go with it, and those are not the surface language. A
    module implementing an interface that declares a field would inherit the rewritten
    declaration and be checked against it -- so `own(x.f, v, 1.0)` would be rejected for
    passing a fraction for an RA-valued field, and a manifest field would be compared
    against `Frac$f.T` rather than against the type the source wrote. Since the standard
    library is a unit of its own, that ruled out a library interface declaring a field at
    all. *)
let type_cu ~ext_hooks ~diagnostics config tbl md =
  let cli_config = cli_config_of config in
  let printers = Rewriter.printers_of_ext_hooks ext_hooks in
  let tbl = SymbolTbl.add_symbol ~diagnostics (ModDef md) tbl in
  let tbl, processed_md =
    Typing.check_module ~tbl ~ext_hooks ~cli_config ~diagnostics md
  in
  Logs.debug (fun m -> m "%a" printers.pr_module processed_md);
  Logs.info (fun m -> m "Type-checking successful.");
  (tbl, processed_md)

(** Elaborates a single, already type-checked compilation unit (see
    [Elaboration.elaborate_module]). Every unit goes through [elaborate_cu] before any
    goes through [lower_cu]. Returns [None] when there is nothing to backend-check
    (`--typeonly`); the `--stats` short-circuit below exits the process directly. *)
let elaborate_cu ~ext_hooks ~diagnostics config tbl (md : Ast.Module.t) front_end_out_chan
    =
  let cli_config = cli_config_of config in
  let printers = Rewriter.printers_of_ext_hooks ext_hooks in

  if config.typecheck_only then (tbl, None)
  else if
    config.prog_stats
    && not
         (Predefs.is_library_qual_ident (QualIdent.from_ident md.mod_decl.mod_decl_name))
  then (
    let _ =
      Logs.debug (fun m ->
          m "Computing stats of module: %a" Ident.pr md.mod_decl.mod_decl_name)
    in
    let prog_stats = Elaboration.compute_stats ~ext_hooks tbl md in

    Logs.app (fun m -> m "\nPROGRAM STATISTICS: \n%a" Elaboration.ProgStats.pr prog_stats);
    Stdlib.exit 0)
  else
    let tbl, md =
      Elaboration.elaborate_module ~tbl ~ext_hooks ~cli_config ~diagnostics md
    in
    Option.iter front_end_out_chan ~f:(fun out_chan ->
        Stdlib.Format.fprintf
          (Stdlib.Format.formatter_of_out_channel out_chan)
          "%a\n" printers.pr_module md);
    (tbl, Some md)

(** Lowers an elaborated compilation unit (see [Lowering.lower_module]), returning it
    together with its lemma call graph. This is kept separate from the actual backend/SMT
    checking ([backend_check_cu] below) so that the full set of tuple sorts a program
    needs (see [Smt.TupleArities]) can be computed from the fully lowered symbol table --
    of both the library and the main program -- before any backend checking (and hence any
    tuple-sort declaration) begins. *)
let lower_cu ~ext_hooks ~diagnostics tbl md lowered_out_chan =
  let printers = Rewriter.printers_of_ext_hooks ext_hooks in

  let tbl, processed_md, lemma_calls =
    Lowering.lower_module ~tbl ~ext_hooks ~diagnostics md
  in

  Logs.debug (fun m -> m "%a" printers.pr_module processed_md);
  Logs.info (fun m -> m "Front-end processing successful.");

  Option.iter lowered_out_chan ~f:(fun out_chan ->
      Stdlib.Format.fprintf
        (Stdlib.Format.formatter_of_out_channel out_chan)
        "%a\n" printers.pr_module processed_md);

  (tbl, (processed_md, lemma_calls))

(** Runs backend/SMT checking over every already-elaborated compilation unit together (the
    library and the program being checked are siblings sharing one symbol table, not one
    nested inside the other -- see [Backend.Dependencies.analyze]'s doc comment -- so they
    have to be checked as one combined call for [Backend.Checker.check_members]'s
    hierarchical scoping to see both sides of that sharing). *)
let backend_check_cu tbl context processed =
  let processed_mds, lemma_calls = List.unzip processed in
  let lemma_calls =
    List.fold lemma_calls ~init:Ast.CallGraph.Graph.empty ~f:Ast.CallGraph.Graph.union
  in
  Backend.Checker.check_module processed_mds lemma_calls tbl context

(** The named assertions and loop invariants of the statement [stmt], with their kinds and
    locations. [contents] gives the specs and statements of an extension's statement (see
    [ExtApi.Ext.stmt_ext_contents]). *)
let rec named_assertions ~contents (stmt : Ast.Stmt.t) : (string * string * Loc.t) list =
  let named_assertions = named_assertions ~contents in
  match stmt.stmt_desc with
  | Block block -> List.concat_map block.block_body ~f:named_assertions
  | Loop loop ->
      List.filter_map loop.loop_contract ~f:(fun spec ->
          Option.map spec.spec_name ~f:(fun name ->
              (name, "invariant", Expr.to_loc spec.spec_form)))
      @ named_assertions loop.loop_prebody
      @ named_assertions loop.loop_postbody
  | Cond cond -> named_assertions cond.cond_then @ named_assertions cond.cond_else
  | Basic (Spec (Assert, { spec_name = Some name; _ })) ->
      [ (name, "assertion", stmt.stmt_loc) ]
  | StmtExt stmt_ext ->
      let specs, stmts = contents stmt_ext in
      List.filter_map specs ~f:(fun (spec : Ast.Stmt.spec) ->
          Option.map spec.spec_name ~f:(fun name -> (name, "assertion", stmt.stmt_loc)))
      @ List.concat_map stmts ~f:named_assertions
  | Basic _ -> []

(** The callables, named assertions and invariants, fields, types, constants and modules
    of the parsed program [md], for their verification status and an outline. The text of
    a callable is the union of the locations of its name, contract and body that lie in
    the file it is declared in. *)
let source_members ~contents (md : Ast.Module.t) :
    Diagnostics.MemberStatus.member list * Diagnostics.MemberStatus.group list =
  let member path (callable : Ast.Callable.t) =
    let decl = callable.call_decl in
    let name_loc = decl.call_decl_loc in
    let body_loc, has_body =
      match callable.call_def with
      | ProcDef { proc_body = Some body } -> ([ body.stmt_loc ], true)
      | FuncDef { func_body = Some body } -> ([ Expr.to_loc body ], true)
      | ProcDef { proc_body = None } | FuncDef { func_body = None } -> ([], false)
    in
    let clause_locs =
      List.map (decl.call_decl_precond @ decl.call_decl_postcond) ~f:(fun spec ->
          Expr.to_loc spec.spec_form)
    in
    let extent =
      List.fold (body_loc @ clause_locs) ~init:name_loc ~f:(fun extent loc ->
          if String.equal (Loc.file_name loc) (Loc.file_name name_loc) then
            Loc.merge extent loc
          else extent)
    in
    let kind =
      match decl.call_decl_kind with
      | Proc -> "proc"
      | Lemma -> if has_body then "lemma" else "axiom"
      | Func -> "func"
      | Pred -> "pred"
      | Invariant -> "inv"
    in
    (* What is checked as it is written; for predicates it depends on how they are
       lowered. *)
    let checked =
      (not (Ast.is_free decl.call_decl_status))
      &&
      match (decl.call_decl_kind, callable.call_def) with
      | (Proc | Lemma), ProcDef { proc_body = Some _ } -> true
      (* Without a body, a function's contract is assumed. *)
      | Func, FuncDef { func_body = Some _ } ->
          not (List.is_empty decl.call_decl_postcond)
      | _ -> false
    in
    let name =
      String.concat ~sep:"." (List.rev (Ident.name decl.call_decl_name :: path))
    in
    let assertions =
      match callable.call_def with
      | ProcDef { proc_body = Some body } ->
          List.map (named_assertions ~contents body) ~f:(fun (label, kind, loc) ->
              {
                Diagnostics.MemberStatus.name = name ^ "." ^ label;
                kind;
                name_loc = loc;
                extent = loc;
                checked = false;
                inherited = false;
              })
      | _ -> []
    in
    { Diagnostics.MemberStatus.name; kind; name_loc; extent; checked; inherited = false }
    :: assertions
  in
  let declaration path kind (name : Ident.t) extent =
    {
      Diagnostics.MemberStatus.name =
        String.concat ~sep:"." (List.rev (Ident.name name :: path));
      kind;
      name_loc = Ident.to_loc name;
      extent;
      checked = false;
      inherited = false;
    }
  in
  (* Accumulates in reverse order. *)
  let rec collect path (members, groups) (md : Ast.Module.t) =
    List.fold md.mod_def ~init:(members, groups) ~f:(fun (members, groups) -> function
      | Ast.Module.SymbolDef (CallDef callable) ->
          (List.rev_append (member path callable) members, groups)
      | SymbolDef (FieldDef field) ->
          (declaration path "field" field.field_name field.field_loc :: members, groups)
      | SymbolDef (TypeDef typ) ->
          (declaration path "type" typ.type_def_name typ.type_def_loc :: members, groups)
      | SymbolDef (ModInst instance) when Option.is_some instance.mod_inst_def ->
          ( declaration path "instance" instance.mod_inst_name instance.mod_inst_loc
            :: members,
            groups )
      | SymbolDef (VarDef var) ->
          ( declaration path "val" var.var_decl.var_name var.var_decl.var_loc :: members,
            groups )
      | SymbolDef (ModDef sub) ->
          let sub_path = Ident.name sub.mod_decl.mod_decl_name :: path in
          let group =
            {
              Diagnostics.MemberStatus.group_name =
                String.concat ~sep:"." (List.rev sub_path);
              group_kind =
                (if sub.mod_decl.mod_decl_is_interface then "interface" else "module");
              group_loc = sub.mod_decl.mod_decl_loc;
            }
          in
          collect sub_path (members, group :: groups) sub
      | _ -> (members, groups))
  in
  let members, groups = collect [] ([], []) md in
  (List.rev members, List.rev groups)

(** What `--only` selects by [name], among the program's [members] and [groups]. *)
let focus_of members groups (name : string) : Backend.CheckerContext.focus =
  let open Diagnostics.MemberStatus in
  let named m = String.equal m.name name in
  match
    ( List.find members ~f:named,
      List.find groups ~f:(fun g -> String.equal g.group_name name) )
  with
  | Some { kind = "assertion" | "invariant"; _ }, _ ->
      (* The assertion's member is the one its name extends. *)
      let member_name = String.rsplit2_exn name ~on:'.' |> fst in
      let label = String.rsplit2_exn name ~on:'.' |> snd in
      let extents =
        List.filter_map members ~f:(fun m ->
            Option.some_if (String.equal m.name member_name) m.extent)
      in
      { extents; assertion = Some label }
  | Some member, _ -> { extents = [ member.extent ]; assertion = None }
  | None, Some group ->
      (* With the lemmas the module is checked for at its name. *)
      { extents = [ group_extent members group; group.group_loc ]; assertion = None }
  | None, None ->
      Error.error Loc.dummy
        (Printf.sprintf "There is no member, module or named assertion %s to verify" name)

(** Parse and check all compilation units in files [file_names]. [extension_mode] picks
    the `--extension` chain: [`Explicit ext] uses [ext] outright; [`Auto] detects it from
    the parsed program's own extension-specific syntax (see [Ext.detect_extension]) before
    the library -- whose sources the choice picks -- is parsed. That's why the program is
    parsed here ahead of the library, the reverse of the order *type-checking* needs (see
    [type_cu]'s doc comment): parsing has no dependency on the library's symbol table,
    only type-checking does. *)
let parse_and_check_all ~extension_mode ~diagnostics config file_names =
  (* Variable which controls whether the
    - `front_end_output.log` (the elaborated program)
    - `lowered_output.log` (the lowered program)
    - `log.smt2`
    files are created.
    At present create them only when in Debug mode and also not in lsp_mode.
   *)
  let external_logging =
    match config.log_level with
    | Some Logs.Debug -> if config.lsp_mode then false else true
    | _ -> false
  in

  let debug_out_chan file_name =
    if external_logging then Some (Stdio.Out_channel.create file_name) else None
  in
  let front_end_out_chan = debug_out_chan "front_end_output.log" in
  let lowered_out_chan = debug_out_chan "lowered_output.log" in

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
              let loc =
                Hashtbl.find include_map file_name |> Option.value ~default:Loc.dummy
              in
              Error.error loc
                (Printf.sprintf "Cannot find file '%s' (referenced by an include)"
                   file_name)
          in
          let includes, md = parse_cu file_dir Predefs.prog_ident lexbuf in

          if config.strict then warn_free_usage ~diagnostics md;

          Stdio.In_channel.close inchan;

          let md =
            (* [is_free] here is set unconditionally for every `include`d file (see
               [parse_cu]) -- there is no `free include` syntax -- so this is the
               compiler's decision, not the user's, and uses [set_unit_free] for the
               same reason the standard library below does. Marking it [UserFree]
               instead used to let a module implementing an interface from an included
               file skip both halves of the conformance check. *)
            if is_free then Ast.Module.set_unit_free md else md
          in

          let parsed = Set.add parsed file_name in

          let to_parse2 = to_parse1 @ includes in
          parse_prog parsed to_parse2 (merge_prog md prog))
        else (
          Logs.debug (fun m -> m "raven.parse_prog: Skipping file %s." file_name);
          parse_prog parsed to_parse1 prog)
  in

  let md =
    parse_prog
      (Set.empty (module String))
      (List.rev_map
         ~f:(fun file_name ->
           let norm_dir = normalizeFilename (Unix.getcwd ()) config.base_dir in
           let norm_file_name = normalizeFilename norm_dir file_name in
           let file_dir =
             if String.(config.base_dir <> "") then norm_dir
             else Stdlib.Filename.dirname norm_file_name
           in
           (file_dir, file_name, false))
         file_names)
      empty_prog
  in

  (* [EXT] Resolve which extension is activated for this run and build the hooks the
     rest of the pipeline dispatches through -- see lib/ext/ext.ml and
     Ast.Rewriter.ext_hooks. Under [`Auto], this is the earliest point the choice can be
     made: it needs [md], and needs to happen before the library (whose sources the
     choice picks) is parsed below. *)
  let chosen_ext =
    match extension_mode with `Explicit ext -> ext | `Auto -> Ext.detect_extension md
  in
  let (module ChosenExt) = Ext.module_map chosen_ext in
  let ext_hooks = Ext.to_ext_hooks (module ChosenExt : ExtApi.Ext) in
  let members, groups = source_members ~contents:ChosenExt.stmt_ext_contents md in
  Diagnostics.set_members diagnostics (members, groups);
  let focus = Option.map config.only ~f:(focus_of members groups) in
  let lib_sources = ChosenExt.lib_sources in
  let unit_sources lib_unit =
    List.filter_map lib_sources ~f:(fun (src_unit, src) ->
        Option.some_if (Poly.equal src_unit lib_unit) src)
  in

  (* Locations inside extension library sources (e.g. well_founded_order.rav) are
     virtual -- there's no real file on disk for Loc.context to fall back to reading.
     Register them so it can find the text the same way it already does for the core
     standard library ([Library.sources]). *)
  Loc.register_sources (List.map lib_sources ~f:snd);

  (* Parse and check standard library *)
  let tbl = SymbolTbl.create () in
  let tbl, lib_typed =
    if config.no_library then (tbl, [])
    else
      let parse_lib_source cu_ident (lib_file_name, lib_source) =
        let lib_source_lexbuf = Lexing.from_string lib_source in
        let _ = Lexer.set_file_name lib_source_lexbuf lib_file_name in
        let _includes, md =
          parse_cu (Stdlib.Filename.dirname lib_file_name) cu_ident lib_source_lexbuf
        in
        (* [set_unit_free], not [set_free]: the standard library is trusted by the
           compiler so it isn't re-verified for every program, which is exactly what
           [MachineFree] means -- as opposed to [UserFree], a `free` the user wrote.
           The two must stay distinguishable: a member inherited from here into a
           user module still owes a definition and a proof, whereas one inherited
           from a user's own `free` declaration does not (see
           [Interfaces.un_free_inherited]). *)
        Ast.Module.set_unit_free md
      in
      let parse_unit cu_ident sources =
        List.fold_right sources ~init:empty_prog ~f:(fun lib_file unit_prog ->
            merge_prog (parse_lib_source cu_ident lib_file) unit_prog)
      in
      (* The modules elaboration and lowering instantiate are units of their own, which
         programs cannot name, after the library they build on. *)
      let units =
        [
          (Predefs.lib_ident, Library.library_sources @ unit_sources ExtApi.Library_unit);
          (Predefs.elaboration_ident, unit_sources ExtApi.Elaboration_unit);
          (Predefs.lowering_ident, [ Library.lowering_source ]);
        ]
      in
      List.fold_map units ~init:tbl ~f:(fun tbl (cu_ident, sources) ->
          type_cu ~ext_hooks ~diagnostics config tbl (parse_unit cu_ident sources))
  in

  let md =
    if config.no_library then md
    else
      let import name =
        Ast.Module.Import
          {
            import_name =
              QualIdent.from_list
                (Predefs.lib_ident
                :: List.map name ~f:(fun name -> Ident.make Loc.dummy name 0));
            import_all = false;
            import_prelude = true;
            import_loc = Loc.dummy;
          }
      in
      { md with mod_def = List.map Library.prelude ~f:import @ md.mod_def }
  in
  let tbl, prog_typed = type_cu ~ext_hooks ~diagnostics config tbl md in

  (* All units are type-checked before any is rewritten -- see [type_cu] -- and
     elaborated before any is lowered -- see [elaborate_cu]. The library goes first
     each time, since processing the program needs the artifacts the library's own
     processing generates. *)
  let typed = lib_typed @ [ prog_typed ] in
  let tbl, elaborated =
    List.fold_map typed ~init:tbl ~f:(fun tbl md ->
        elaborate_cu ~ext_hooks ~diagnostics config tbl md front_end_out_chan)
  in
  let tbl, processed =
    List.fold_map (List.filter_opt elaborated) ~init:tbl ~f:(fun tbl md ->
        lower_cu ~ext_hooks ~diagnostics tbl md lowered_out_chan)
  in

  begin
    (* Logs.debug (fun m -> m "Final symboltbl.tbl_symbols: %a" (Util.Print.pr_list_comma QualIdent.pr) (Map.keys tbl.tbl_symbols)); *)
    (match processed with
    | [] -> (* `--typeonly`: nothing left to backend-check *) ()
    | _ ->
        (* Only now -- once both the library and the main program have been fully
        elaborated -- do we know every tuple sort ([$tuple_n]) the program actually
        needs (see Smt.TupleArities), so this is the earliest point at which we
        can declare them. *)
        let arities = Smt.TupleArities.of_symbols (Map.data tbl.tbl_symbols) in
        let solver_session =
          Smt.SmtSolver.init ~logging:external_logging config.smt_timeout
        in
        Stdlib.Fun.protect ~finally:(fun () -> Smt.SmtSolver.stop solver_session)
        @@ fun () ->
        Backend.SmtPreamble.initialize solver_session ~diagnostics:config.smt_diagnostics
          ~timeout:config.smt_timeout;
        Backend.SmtPreamble.declare_tuple_sorts solver_session arities;
        let context =
          Backend.CheckerContext.create ?focus ~counterexamples:config.counterexamples
            ~diagnostics solver_session
        in
        let (_ : Backend.CheckerContext.context) =
          backend_check_cu tbl context processed
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
  Arg.(value & pos_all non_dir_file [] & info [] ~docv:"INPUT" ~doc)

let no_greeting =
  let doc = "Suppress greeting." in
  Arg.(value & flag & info [ "shh" ] ~doc)

let no_library =
  let doc = "Skip standard library." in
  Arg.(value & flag & info [ "nostdlib" ] ~doc)

let prog_stats =
  let doc =
    "Output only program stats: concrete instruction steps, ghost instruction steps, and \
     number of specification formulae"
  in
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

let lsp_annotations =
  let doc =
    "With --lsp-mode, print an object with the errors, included-file dependencies and \
     annotations for the editor, such as the contracts that members inherit from \
     interfaces, the verification status of each member, and what the names the program \
     uses refer to."
  in
  Arg.(value & flag & info [ "lsp-annotations" ] ~doc)

let base_dir =
  let doc =
    "Base directory for resolving include directives. Default: current working directory."
  in
  Arg.(value & opt string "" & info [ "base-dir" ] ~doc)

let smt_timeout =
  let doc = "Timeout for SMT solver in ms." in
  Arg.(value & opt int 10000 & info [ "smt-timeout" ] ~doc)

let max_errors =
  let doc =
    "Stop after reporting this many errors; 0 means no limit. Default: 20, but no limit \
     with --lsp-mode."
  in
  Arg.(value & opt (some int) None & info [ "max-errors" ] ~doc)

let only =
  let doc =
    "Verify only the member, module or interface of this qualified name, such as M.p, or \
     only the assertion of this name in a member, such as M.p.a for `assert a: ...` in \
     M.p, and assume the others."
  in
  Arg.(value & opt (some string) None & info [ "only" ] ~docv:"NAME" ~doc)

let counterexamples =
  let doc =
    "For a failed check, show the values of the variables, and of the fields of the \
     references among them, at the failure, and the arms the failing path takes at the \
     conditionals before it. When the solver could not decide the check, the \
     counterexample is only possible: it may contradict quantified facts."
  in
  Arg.(value & flag & info [ "counterexamples" ] ~doc)

let extension_mode =
  let doc =
    "Extension mode: default, eris, or auto. \"auto\" detects the right one from the \
     input program's own extension-specific syntax before the library, whose sources the \
     choice picks, is parsed; a program using no extension-specific syntax falls back to \
     \"default\"."
  in
  let supported_exts =
    ("auto", "auto") :: List.map ~f:(fun (e, _) -> (e, e)) Ext.ext_map
  in
  Arg.(value & opt (enum supported_exts) "default" & info [ "extension" ] ~doc)

let strict =
  let doc =
    "Warn about anything the verifier assumes rather than checks: recursive \
     lemmas/functions and loops in lemmas missing `decreases` clauses, explicit user use \
     of `free`, and `atomic { ... }` blocks, whose bodies are taken to be a single \
     machine step on trust. Library sources are excluded."
  in
  Arg.(value & flag & info [ "strict" ] ~doc)

let dump_library =
  let doc =
    "Write the embedded library sources (the standard library plus the active \
     extension's) into DIR, reproducing their paths, and exit. The files are \
     byte-identical to what this binary verifies against."
  in
  Arg.(value & opt (some string) None & info [ "dump-library" ] ~docv:"DIR" ~doc)

let print_library_source =
  let doc =
    "Write the embedded library source named PATH (as reported in diagnostics, e.g. \
     lib/library/resource_algebra.rav) to stdout, and exit. Lets an editor display a \
     library location that has no file on disk."
  in
  Arg.(value & opt (some string) None & info [ "print-library-source" ] ~docv:"PATH" ~doc)

let manifest =
  let doc =
    "Print, as one line of JSON, what this binary is and what a client can expect of it \
     -- its release version, the version of the machine-readable interface driven by \
     --lsp-mode, and the oldest Z3 it works against -- and exit. An editor integration \
     that can fetch verifier builds it was not shipped with reads this both from a \
     release and from a binary it already has, to decide whether it can drive it."
  in
  Arg.(value & flag & info [ "manifest" ] ~doc)

(** What [--manifest] emits. Also published as a release asset, so a client can check a
    release before spending a download on it; keep the two producing the same shape. *)
let manifest_json =
  `Assoc
    [
      ("version", `String Config.version);
      ("lsp_protocol", `Int Config.lsp_protocol_version);
      ("min_z3", `String Config.min_z3_version);
    ]

let greeting = "Raven version " ^ Config.version

let anchor_lsp_diagnostic err =
  (* Follow a location back through the `include` directives that pulled its file in,
     to a location in the file actually being checked. *)
  let rec anchor_loc loc =
    match Hashtbl.find include_map (Loc.file_name loc) with
    | Some loc1 -> anchor_loc loc1
    | None -> loc
  in
  (* An LSP diagnostic is reported against one document and is displayed at its range
     *in that document*, so a primary error whose own location lies in an included file
     has to be anchored at the `include` that brought it in -- otherwise the editor
     would show it at those coordinates in the wrong file. The message keeps saying what
     went wrong, and names where it really is.

     [RelatedLoc] entries are exempt: LSP's `relatedInformation` carries a URI per entry,
     so each one can point at its true file. Those are what make the offending line
     reachable, and rewriting them (as this used to, replacing both the location and the
     message with "originates in included file") is what made them useless. *)
  let anchor ((kind, loc, msg) as err) =
    match kind with
    | Error.RelatedLoc -> err
    | _ ->
        let loc' = anchor_loc loc in
        if Loc.(loc' = loc) then err
        else
          ( kind,
            loc',
            Printf.sprintf
              !"%{String} (in included file %{String}, line %{Int})"
              msg (Loc.display_file_name loc) (Loc.start_line loc) )
  in
  anchor err

(** With `--lsp-annotations`, include editor annotations and dependency filenames. *)
let print_lsp_output config ~diagnostics errs =
  let errs =
    List.map (Diagnostics.warnings diagnostics @ errs) ~f:anchor_lsp_diagnostic
  in
  if config.lsp_annotations then
    let references, symbols = Diagnostics.references_to_json diagnostics in
    Stdlib.print_endline
      (Yojson.Safe.to_string
         (`Assoc
            [
              ("errors", `List (List.map errs ~f:Error.to_lsp_json));
              ("annotations", Diagnostics.annotations_to_json diagnostics);
              ("members", Diagnostics.members_to_json diagnostics);
              ("references", references);
              ("symbols", symbols);
              ( "dependencies",
                `List
                  (Hashtbl.keys include_map
                  |> List.sort ~compare:String.compare
                  |> List.map ~f:(fun file -> `String file)) );
            ]))
  else Stdlib.print_endline (Error.errors_to_lsp_string errs)

let print_errors config ~diagnostics errs =
  if config.lsp_mode then begin
    print_lsp_output config ~diagnostics errs;
    Stdlib.exit 0
  end
  else begin
    List.iter errs ~f:(fun e -> Logs.err (fun m -> m !"%{Error}" e));
    Logs.debug (fun m ->
        m "\n---------\n%s" @@ Backtrace.to_string (Backtrace.Exn.most_recent ()));
    Stdlib.exit 1 (* duplicates error output: `Error (false, "") *)
  end

(** Serves the embedded library sources to whoever needs the text of a location that has
    no file on disk: `--dump-library` writes them all out, `--print-library-source` emits
    one. Both run after the extension is resolved, so the active extension's own library
    is included, and both use exactly the bytes this binary verifies against. *)
let serve_library_sources ~lib_sources ~dump_library ~print_library_source =
  let sources = Library.sources @ lib_sources in
  let dumped =
    Option.map dump_library ~f:(fun dir ->
        List.iter sources ~f:(fun (name, content) ->
            (* [Loc.join_path], not [Filename.concat]: keeps the reproduced tree
               '/'-separated on every platform, matching the paths the sources are named
               and reported by. *)
            let target = Loc.join_path dir name in
            let rec mkdirs d =
              if not (Stdlib.Sys.file_exists d) then begin
                mkdirs (Stdlib.Filename.dirname d);
                Unix.mkdir d 0o755
              end
            in
            mkdirs (Stdlib.Filename.dirname target);
            Stdio.Out_channel.write_all target ~data:content;
            Logs.app (fun m -> m "%s" target)))
  in
  let printed =
    Option.map print_library_source ~f:(fun name ->
        match List.Assoc.find sources ~equal:String.equal name with
        | Some content ->
            (* Binary mode: on Windows the default text mode would rewrite every '\n' on
               the way out, so an editor displaying this would not be displaying the
               bytes this binary actually verified -- the one property the flag exists to
               guarantee. `.gitattributes` pins these files to LF for the same reason. *)
            Stdlib.set_binary_mode_out Stdlib.stdout true;
            Stdlib.print_string content
        | None ->
            Logs.err (fun m ->
                m "No library source named '%s'. Known sources: %s" name
                  (String.concat ~sep:", " (List.map sources ~f:fst))))
  in
  Option.is_some dumped || Option.is_some printed

let main () input_files no_greeting no_library typecheck_only lsp_mode lsp_annotations
    base_dir prog_stats smt_timeout smt_diagnostics max_errors only counterexamples
    extension_mode_arg strict dump_library print_library_source manifest =
  if manifest then begin
    (* Payload rather than logging, so it survives -q and needs no --shh: whoever asks
       is a program parsing this one line. *)
    Stdlib.print_endline (Yojson.Safe.to_string manifest_json);
    Stdlib.exit 0
  end;
  if not no_greeting then Logs.app (fun m -> m "%s" greeting) else ();
  let config =
    {
      no_library;
      typecheck_only;
      lsp_mode;
      lsp_annotations;
      prog_stats;
      base_dir;
      smt_timeout;
      smt_diagnostics;
      max_errors;
      log_level = Logs.level ();
      strict;
      only;
      counterexamples;
    }
  in
  (* [EXT] "auto" is resolved from the input program's own syntax once it's parsed --
     see [parse_and_check_all] -- since the choice also picks which extension's library
     sources get parsed, and the program is parsed before the library.
     [--dump-library]/[--print-library-source] below have no program to detect from, so
     "auto" there just falls back to the plain "default" chain, same as a program using
     no extension-specific syntax would. *)
  let explicit_extension_mode =
    if String.(extension_mode_arg = "auto") then None
    else Some (List.Assoc.find_exn ~equal:String.( = ) Ext.ext_map extension_mode_arg)
  in
  let (module LibraryExt) =
    Ext.module_map (Option.value explicit_extension_mode ~default:Ext.ProphecyExt)
  in
  if
    serve_library_sources
      ~lib_sources:(List.map LibraryExt.lib_sources ~f:snd)
      ~dump_library ~print_library_source
  then `Ok ()
  else
    let extension_mode : [ `Explicit of Ext.supported_extensions | `Auto ] =
      match explicit_extension_mode with Some ext -> `Explicit ext | None -> `Auto
    in
    let diagnostics =
      Diagnostics.create ?max_errors:(max_errors_of config)
        ~collect_warnings:config.lsp_mode
        ~reference_files:
          (if config.lsp_mode && config.lsp_annotations then input_files else [])
        ()
    in
    try
      let result = parse_and_check_all ~extension_mode ~diagnostics config input_files in
      if
        config.lsp_mode
        && (config.lsp_annotations
           || not (List.is_empty (Diagnostics.warnings diagnostics)))
      then print_lsp_output config ~diagnostics [];
      `Ok result
    with
    | Unix.Unix_error (err, _, prog) ->
        let msg =
          Printf.sprintf
            "Could not start '%s' (%s). Raven requires Z3 (>= %s) to be installed and on \
             your PATH."
            prog (Unix.error_message err) Config.min_z3_version
        in
        print_errors config ~diagnostics [ (Generic, Loc.dummy, msg) ]
    | (Sys_error _ | Failure _ | Invalid_argument _ | Assert_failure _) as exn ->
        let msg = String.map ~f:(function '"' -> '\'' | c -> c) (Exn.to_string exn) in
        let pos =
          match input_files with
          | file :: _ ->
              Loc.make
                Lexing.{ pos_fname = file; pos_bol = 0; pos_cnum = 0; pos_lnum = 1 }
                Lexing.{ pos_fname = file; pos_bol = 0; pos_cnum = 0; pos_lnum = 1 }
          | _ -> Loc.dummy
        in
        print_errors config ~diagnostics [ (Internal, pos, msg) ]
    | Error.Msg es -> print_errors config ~diagnostics es

let main_cmd =
  let info = Cmd.info "raven" ~version:Config.version in
  Cmd.v info
    Term.(
      ret
        (const main $ setup_config $ input_file $ no_greeting $ no_library
       $ typecheck_only $ lsp_mode $ lsp_annotations $ base_dir $ prog_stats $ smt_timeout
       $ smt_diagnostics $ max_errors $ only $ counterexamples $ extension_mode $ strict
       $ dump_library $ print_library_source $ manifest))

let () = Stdlib.exit (Cmd.eval main_cmd)
