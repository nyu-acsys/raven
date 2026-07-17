type supported_extensions =
  | DefaultExt
  | ErisExt
  | ProphecyExt

let ext_map = [
  ("default", ProphecyExt);
  ("eris", ErisExt);
  ("prophecy", ProphecyExt)
]

module DefaultExtInstance = DefaultExt.DefaultExt
module ListExtInstance = ListExt.ListExt(DefaultExtInstance)
module AtomicExtInstance = AtomicExt.AtomicExt(ListExtInstance)

(* Core Raven *)
module RavenCore: ExtApi.Ext = AtomicExtInstance

(* ProphecyExt *)
module ProphecyExtInstance = ProphecyExt.ProphecyExt(AtomicExtInstance)

(* ErrorCredits *)
module ErrorCreditsExtInstance = ErrorCreditsExt.ErrorCreditsExt(AtomicExtInstance)
module SampleExtInstance = SampleExt.SampleExt(ErrorCreditsExtInstance)

let module_map ext = match ext with
| DefaultExt -> (module RavenCore: ExtApi.Ext)
| ErisExt -> (module ErrorCreditsExtInstance: ExtApi.Ext)
| ProphecyExt -> (module ProphecyExtInstance: ExtApi.Ext)

(** Converts a chosen extension into the [Ast.Rewriter.ext_hooks] value the rest of
    the pipeline reads out of the [Rewriter] monad's state. *)
let to_ext_hooks (ext : (module ExtApi.Ext)) : Ast.Rewriter.ext_hooks =
  let (module Ext) = ext in
  {
    type_ext_to_name = Ext.type_ext_to_name;
    expr_ext_to_string = Ext.expr_ext_to_string;
    pr_stmt_ext = Ext.pr_stmt_ext;
    stmt_ext_symbols = Ext.stmt_ext_symbols;
    stmt_ext_local_vars_modified = Ext.stmt_ext_local_vars_modified;
    stmt_ext_fields_accessed = Ext.stmt_ext_fields_accessed;
    expr_ext_rewrite_types = Ext.expr_ext_rewrite_types;
    stmt_ext_rewrite_types = Ext.stmt_ext_rewrite_types;
    type_check_type_expr = Ext.type_check_type_expr;
    type_check_expr = Ext.type_check_expr;
    type_check_stmt = Ext.type_check_stmt;
    rewrite_type_ext = Ext.rewrite_type_ext;
    rewrite_expr_ext = Ext.rewrite_expr_ext;
    rewrite_stmt_ext = Ext.rewrite_stmt_ext;
    ext_local_vars = Ext.ext_local_vars;
  }
