%{

open Ext.ListExtInstance

%}

%token LIST

%%

%public typeExt:
| LIST; LBRACKET; elem_tp = type_expr; RBRACKET { 
  Type.mk_app ~loc:(Loc.make $startpos $endpos) (TypeExt (ListConstr)) [elem_tp] }

%public unary_exprExt:
| f = list_expr_ext { f }

list_expr_ext:
| LIST; DOT; call = IDENT; LPAREN; es=expr_list; RPAREN {
  Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt (ListExpr call) ) es
}
| LIST; DOT; call = IDENT; LPAREN; RPAREN {
  Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt (ListExpr call) ) []
}
// Add infix cons support; throwing shift/reduce conflicts:
// | e1=expr; COLONCOLON; e2=expr {
//   Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt (ListExpr ListPredefs.cons_ident) ) [e1; e2]
// }

| LIST; DOT; call = IDENT {
  Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt (ListExpr call)) []
}