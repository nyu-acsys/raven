type supported_extensions = 
  | DefaultExt 
  | ErisExt 
  | ProphecyExt

let ext_map = [
  ("default", DefaultExt);
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

(* let ext: supported_extensions ref = ref (DefaultExt) *)

let ext : (module ExtApi.Ext) ref = 
  ref (module RavenCore : ExtApi.Ext)

let module_map ext = match ext with
| DefaultExt -> (module RavenCore: ExtApi.Ext)
| ErisExt -> (module ErrorCreditsExtInstance: ExtApi.Ext)
| ProphecyExt -> (module ProphecyExtInstance: ExtApi.Ext)

(* module Ext = (val (module_map !ext) : ExtApi.Ext) *)

(* module Ext = struct
  let do_something x =
    let (module M) = module_map !ext in
    M.do_something x
end *)


let refresh_ptrs () =
  let (module Ext) = !ext in
  Ast.Type.type_ext_to_name := Ext.type_ext_to_name;
  Ast.Expr.expr_ext_to_string := Ext.expr_ext_to_string;
  Ast.Stmt.pr_stmt_ext := Ext.pr_stmt_ext;
  Ast.Stmt.stmt_ext_symbols := Ext.stmt_ext_symbols;
  Ast.Stmt.stmt_ext_local_vars_modified := Ext.stmt_ext_local_vars_modified;
  Ast.Stmt.stmt_ext_fields_accessed := Ext.stmt_ext_fields_accessed;
  Ast.Rewriter.stmt_ext_rewrite_types_ref := Ext.stmt_ext_rewrite_types;
  Ast.Rewriter.expr_ext_rewrite_types_ref := Ext.expr_ext_rewrite_types;
  ()

let overwrite_ext (new_ext: (module ExtApi.Ext)) =
  ext := new_ext;
  refresh_ptrs ();
  ()

let _ =
  refresh_ptrs();