%{

open Ext.SeqExtInstance

(* The slice of [e] from [lo] to [hi], as in Viper, where `s[lo..hi]` is `s[..hi][lo..]`. *)
let slice loc e lo hi =
  let loc = Loc.merge (Expr.to_loc e) loc in
  let e =
    match hi with
    | Some hi -> Expr.mk_app ~typ:Type.any ~loc (ExprExt SeqTake) [ e; hi ]
    | None -> e
  in
  match lo with
  | Some lo -> Expr.mk_app ~typ:Type.any ~loc (ExprExt SeqDrop) [ e; lo ]
  | None -> e

%}

%token DOTDOT

%%

(* A sequence literal `[|e1, ..., en|]`, with `[||]` for the empty sequence, after the
   set literal `{|e1, ..., en|}`. *)
%public compr_expr:
| LBRACKETPIPE; es = separated_list(COMMA, expr); RBRACKETPIPE {
    Expr.mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) (ExprExt SeqLit) es
  }

(* The slices `s[..hi]`, `s[lo..]` and `s[lo..hi]`. *)
%public lookup_or_update_opt:
| LBRACKET; DOTDOT; hi = expr; RBRACKET; cont = lookup_or_update_opt {
    fun e -> cont (slice (Loc.make $symbolstartpos $endpos) e None (Some hi))
  }
| LBRACKET; lo = expr; DOTDOT; RBRACKET; cont = lookup_or_update_opt {
    fun e -> cont (slice (Loc.make $symbolstartpos $endpos) e (Some lo) None)
  }
| LBRACKET; lo = expr; DOTDOT; hi = expr; RBRACKET; cont = lookup_or_update_opt {
    fun e -> cont (slice (Loc.make $symbolstartpos $endpos) e (Some lo) (Some hi))
  }
