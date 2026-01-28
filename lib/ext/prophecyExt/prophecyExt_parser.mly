%{

open Ext.ProphecyExtInstance

%}

%token PROPH NEW1 RESOLVE PROPHECY

%%

%public type_expr:
| PROPH {
  Type.mk_app ~loc:(Loc.make $startpos $endpos) (TypeExt ProphId) []
}

%public unary_expr:
| PROPH DOT PROPHECY; LPAREN; e1=expr; COMMA; e2=expr; RPAREN {
  Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt ProphResource) [e1; e2]
}

%public assign_rhs:
| PROPH DOT NEW LBRACKET t=type_expr RBRACKET {
  function
  | [proph_id; proph_val], _ ->
    Stmt.(Basic (StmtExt ((NewProph (false, t)), [proph_id; proph_val]))), None
  | _, _ ->
    Error.syntax_error (Type.to_loc t) "[EXT] ProphecyExt: Expected prophecy id variable and prophecy value variable on left-hand side of NewProph"
}
| PROPH DOT NEW1 LBRACKET t=type_expr RBRACKET {
  function
  | [proph_id; proph_val], _ ->
    Stmt.(Basic (StmtExt ((NewProph (true, t)), [proph_id; proph_val]))), None
  | _, _ ->
    Error.syntax_error (Type.to_loc t) "[EXT] ProphecyExt: Expected prophecy id variable and prophecy value variable on left-hand side of NewProph"
}

%public stmt_ext:
| PROPH DOT RESOLVE; LPAREN; e1=expr; COMMA; e2=expr; RPAREN SEMICOLON { [Stmt.Basic (StmtExt (ResolveProph, [e1; e2]))]}
