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
      Stmt.(Basic (StmtExt (RandEven, args))), Some (Expr.mk_int 0)
    | e :: _, _ -> Error.syntax_error (Expr.to_loc e) "Expected single variable on left-hand side of RandVal"
    | [], _ -> assert false 
}