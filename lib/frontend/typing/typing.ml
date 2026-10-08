(** Type checking: the entry points used by the rest of the pipeline. *)

open Base
open Ast
open TypingMonad

let check_module ?(tbl = SymbolTbl.create ()) ?ext_hooks ?cli_config (m : Module.t) =
  assert (SymbolTbl.curr_is_root tbl);
  let tbl, m =
    Rewriter.eval ?ext_hooks ?cli_config
      (fun st ->
        let st, _ = Rewriter.enter_module m st in
        let st, m = run_typing (ModuleTyping.check m) st in
        let st, m = Rewriter.exit_module m st in
        (st, m))
      tbl
  in
  (tbl, m)

let check_symbol (symbol : Module.symbol) : Module.symbol Rewriter.t =
  let open Rewriter.Syntax in
  let* symbol =
    run_typing
      (match symbol with
      | Module.TypeDef type_def -> ModuleTyping.check_type_def type_def
      | Module.VarDef var_def -> ModuleTyping.check_var var_def
      | Module.FieldDef field_def -> ModuleTyping.check_field field_def
      | Module.ConstrDef _ | Module.DestrDef _ ->
          Rewriter.return
            symbol (* These should not occur directly in a module definition *)
      | Module.CallDef call_def -> CallableTyping.check call_def
      | Module.ModDef mod_def ->
          let* _ = Rewriter.enter_module mod_def
          and* mod_def = ModuleTyping.check mod_def in
          let+ mod_def = Rewriter.exit_module mod_def in
          Module.ModDef mod_def
      | Module.ModInst mod_inst ->
          (* TODO: Implement checking for mod_inst too *)
          Rewriter.return symbol)
  in

  let+ _ = Rewriter.set_symbol symbol in
  symbol

let _ =
  Rewriter.check_symbol_ref := check_symbol;
  (Rewriter.expand_type_expr_ref := fun tp -> run_typing (TypeExpr.expand_type_expr tp));
  Rewriter.check_stmt_ref :=
    fun call_decl stmt disam_tbl -> run_typing (StmtTyping.check call_decl stmt disam_tbl)
