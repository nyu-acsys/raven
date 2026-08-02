%{

open Ext.SampleExtInstance

%}

%token RANDEVEN

%%

%public assign_rhs:
| RANDEVEN LPAREN n_expr = expr RPAREN {
  function
    | [Expr.(App (Var qual_ident, [], _)) as e], is_init
      when QualIdent.is_local qual_ident ->
      let args = e :: n_expr :: [] in
      Stmt.(Basic (BasicStmtExt (RandEven, args))), Some (Expr.mk_int 0)
    | e :: _, _ -> Error.syntax_error (Expr.to_loc e) "Expected a single local variable on the left-hand side of 'randEven(...)'"
    | [], _ -> assert false 
}