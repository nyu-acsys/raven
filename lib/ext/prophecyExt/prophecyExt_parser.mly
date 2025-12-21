%{

open Ext.ProphecyExtInstance

%}

%token NEWPROPH NEWPROPH1 RESOLVEPROPH PROPHECY PROPHID

%%

%public typeExt:
| PROPHID {
  Type.mk_app ~loc:(Loc.make $startpos $endpos) (TypeExt ProphId) []
}

%public unary_exprExt:
| f = proph_expr_ext { f }

proph_expr_ext:
| PROPHECY; LPAREN; e1=expr; COMMA; e2=expr; RPAREN {
  Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt ProphResource) [e1; e2]
}

%public assignExt:
| NEWPROPH LBRACKET t=type_expr RBRACKET {
  function
  | [proph_id; proph_val], _ ->
    Stmt.(Basic (StmtExt ((NewProph (false, t)), [proph_id; proph_val]))), None
  | _, _ ->
    Error.syntax_error (Type.to_loc t) "[EXT] ProphecyExt: Expected prophecy id variable and prophecy value variable on left-hand side of NewProph"
}
| NEWPROPH1 LBRACKET t=type_expr RBRACKET {
  function
  | [proph_id; proph_val], _ ->
    Stmt.(Basic (StmtExt ((NewProph (true, t)), [proph_id; proph_val]))), None
  | _, _ ->
    Error.syntax_error (Type.to_loc t) "[EXT] ProphecyExt: Expected prophecy id variable and prophecy value variable on left-hand side of NewProph"
}

%public stmtExt:
| RESOLVEPROPH; LPAREN; e1=expr; COMMA; e2=expr; RPAREN SEMICOLON { [Stmt.Basic (StmtExt (ResolveProph, [e1; e2]))]}
