%{

open Ext.ListExtInstance
  
%}

%token LIST

%%


%public type_expr:
| LIST; LBRACKET; elem_tp = type_expr; RBRACKET { 
  Type.mk_app ~loc:(Loc.make $startpos $endpos) (TypeExt (ListConstr)) [elem_tp] }

%public unary_expr:
| LIST; DOT; call = IDENT; es_opt = option(delimited(LPAREN, separated_list(COMMA, expr), RPAREN)) {
  let es = Option.value es_opt ~default:[] in
  Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt (ListExpr call) ) es
}
// Add infix cons support; throwing shift/reduce conflicts:
// | e1=expr; COLONCOLON; e2=expr {
//   Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt (ListExpr ListPredefs.cons_ident) ) [e1; e2]
// }

%public right_assoc_binary_op:
| COLONCOLON { ExprExt (ListExpr ListPredefs.cons_ident) }
