%{

open Ext.SeqExtInstance

%}

%%

(* A sequence literal `[|e1, ..., en|]`, with `[||]` for the empty sequence, after the
   set literal `{|e1, ..., en|}`. *)
%public compr_expr:
| LBRACKETPIPE; es = separated_list(COMMA, expr); RBRACKETPIPE {
    Expr.mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) (ExprExt SeqLit) es
  }
