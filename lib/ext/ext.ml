module DefaultExtInstance = DefaultExt.DefaultExt;;
module ListExtInstance = ListExt.ListExt(DefaultExtInstance);;
module ProphecyExtInstance = ProphecyExt.ProphecyExt(ListExtInstance);;
module AtomicExtInstance = AtomicExt.AtomicExt(ProphecyExtInstance);;
module ErrorCreditsExtInstance = ErrorCreditsExt.ErrorCreditsExt(AtomicExtInstance);;

module Ext = ErrorCreditsExtInstance;;

module _ : ExtApi.Ext = Ext;;

Ast.Type.type_ext_to_name := Ext.type_ext_to_name;;
Ast.Expr.expr_ext_to_string := Ext.expr_ext_to_string;;
Ast.Stmt.pr_stmt_ext := Ext.pr_stmt_ext;;
Ast.Stmt.stmt_ext_symbols := Ext.stmt_ext_symbols;;
Ast.Stmt.stmt_ext_local_vars_modified := Ext.stmt_ext_local_vars_modified;;
Ast.Stmt.stmt_ext_fields_accessed := Ext.stmt_ext_fields_accessed;;