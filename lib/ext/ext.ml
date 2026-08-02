open Base
open Ast

type supported_extensions =
  | DefaultExt
  | ErisExt
  | ProphecyExt

let ext_map = [
  ("default", ProphecyExt);
  ("eris", ErisExt);
]

module DefaultExtInstance = DefaultExt.DefaultExt
module ListExtInstance = ListExt.ListExt(DefaultExtInstance)
module AtomicExtInstance = AtomicExt.AtomicExt(ListExtInstance)

(* DecreasesExt is folded in unconditionally (like AtomicExt above), rather than being
   one more mutually-exclusive `--extension` choice: termination checking via
   `decreases` clauses is orthogonal to which resource-algebra extension is active, so
   it must be available under `default` and `eris` alike. *)
module DecreasesExtInstance = DecreasesExt.DecreasesExt(AtomicExtInstance)

(* AssertWithExt (`assert e with { ... }`) is folded in unconditionally too, for the
   same reason as DecreasesExt above: it's a core-language proof construct, orthogonal
   to which resource-algebra extension is active. *)
module AssertWithExtInstance = AssertWithExt.AssertWithExt(DecreasesExtInstance)

(* MatchExt (ADT recognizer test / `match`) is folded in unconditionally too, for the
   same reason as DecreasesExt/AssertWithExt above: ADT ergonomics is orthogonal to
   which resource-algebra extension is active. It sits above ListExtInstance in the
   chain (like every other link here) so that its own generic `TypeExt` resolution
   (see MatchExt.as_data_type) can delegate to ListExt's `rewrite_type_ext` case to
   resolve `List[T]` scrutinees, without depending on ListExt's internals directly. *)
module MatchExtInstance = MatchExt.MatchExt(AssertWithExtInstance)

(* Core Raven *)
module RavenCore: ExtApi.Ext = MatchExtInstance

(* ProphecyExt *)
module ProphecyExtInstance = ProphecyExt.ProphecyExt(MatchExtInstance)

(* ErrorCredits *)
module ErrorCreditsExtInstance = ErrorCreditsExt.ErrorCreditsExt(MatchExtInstance)
module SampleExtInstance = SampleExt.SampleExt(ErrorCreditsExtInstance)

let module_map ext = match ext with
| DefaultExt -> (module RavenCore: ExtApi.Ext)
| ErisExt -> (module ErrorCreditsExtInstance: ExtApi.Ext)
| ProphecyExt -> (module ProphecyExtInstance: ExtApi.Ext)

(** Every chain reachable through a `--extension` flag, paired with that flag's name --
    i.e. exactly [ext_map], but with each tag already resolved to its module. Used only
    to build the [suggest_extension_for_*] functions below: independent of whichever
    chain is actually active for this run, so a wrong-flag error can point at whichever
    *other* chain would have worked. *)
let known_extensions : (string * (module ExtApi.Ext)) list =
  List.map ext_map ~f:(fun (name, tag) -> (name, module_map tag))

(** Given a lookup of one extension-kind's own [_is_recognized] field out of a module,
    finds the first (in [ext_map] order) `--extension` flag whose chain recognizes
    [tag], if any. *)
let suggest_extension (is_recognized : (module ExtApi.Ext) -> 'a -> bool) (tag : 'a) : string option =
  List.find_map known_extensions ~f:(fun (name, m) -> if is_recognized m tag then Some name else None)

let suggest_extension_for_type_ext (type_ext : Type.type_ext) : string option =
  suggest_extension (fun (module M : ExtApi.Ext) -> M.type_ext_is_recognized) type_ext

let suggest_extension_for_expr_ext (expr_ext : Expr.expr_ext) : string option =
  suggest_extension (fun (module M : ExtApi.Ext) -> M.expr_ext_is_recognized) expr_ext

let suggest_extension_for_stmt_ext (stmt_ext : Stmt.stmt_ext) : string option =
  suggest_extension (fun (module M : ExtApi.Ext) -> M.stmt_ext_is_recognized) stmt_ext

let suggest_extension_for_contract_ext (contract_ext : Stmt.contract_ext) : string option =
  suggest_extension (fun (module M : ExtApi.Ext) -> M.contract_ext_is_recognized) contract_ext

(** Converts a chosen extension into the [Ast.Rewriter.ext_hooks] value the rest of
    the pipeline reads out of the [Rewriter] monad's state. *)
let to_ext_hooks (ext : (module ExtApi.Ext)) : Ast.Rewriter.ext_hooks =
  let (module Ext) = ext in
  {
    type_ext_to_name = Ext.type_ext_to_name;
    expr_ext_to_string = Ext.expr_ext_to_string;
    pr_basic_stmt_ext = Ext.pr_basic_stmt_ext;
    contract_ext_to_string = Ext.contract_ext_to_string;
    basic_stmt_ext_symbols = Ext.basic_stmt_ext_symbols;
    basic_stmt_ext_local_vars_modified = Ext.basic_stmt_ext_local_vars_modified;
    basic_stmt_ext_fields_accessed = Ext.basic_stmt_ext_fields_accessed;
    pr_stmt_ext = Ext.pr_stmt_ext;
    stmt_ext_symbols = Ext.stmt_ext_symbols;
    stmt_ext_local_vars_modified = Ext.stmt_ext_local_vars_modified;
    stmt_ext_fields_accessed = Ext.stmt_ext_fields_accessed;
    suggest_extension_for_type_ext;
    suggest_extension_for_expr_ext;
    suggest_extension_for_stmt_ext;
    suggest_extension_for_contract_ext;
    expr_ext_rewrite_types = Ext.expr_ext_rewrite_types;
    basic_stmt_ext_rewrite_types = Ext.basic_stmt_ext_rewrite_types;
    stmt_ext_rewrite = Ext.stmt_ext_rewrite;
    contract_ext_rewrite_exprs = Ext.contract_ext_rewrite_exprs;
    disambiguate_expr_ext = Ext.disambiguate_expr_ext;
    type_check_type_expr = Ext.type_check_type_expr;
    type_check_expr = Ext.type_check_expr;
    type_check_basic_stmt = Ext.type_check_basic_stmt;
    type_check_stmt_ext = Ext.type_check_stmt_ext;
    type_check_contract_ext = Ext.type_check_contract_ext;
    check_contract_ext_group_compatible = Ext.check_contract_ext_group_compatible;
    rewrite_type_ext = Ext.rewrite_type_ext;
    rewrite_expr_ext = Ext.rewrite_expr_ext;
    rewrite_basic_stmt_ext = Ext.rewrite_basic_stmt_ext;
    rewrite_stmt_ext = Ext.rewrite_stmt_ext;
    rewrite_contract_ext_call = Ext.rewrite_contract_ext_call;
    rewrite_callable_entry = Ext.rewrite_callable_entry;
    rewrite_contract_ext_loop_transfer = Ext.rewrite_contract_ext_loop_transfer;
  }
