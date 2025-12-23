%{

open Ext.ErrorCreditsExtInstance

%}

%token ERRORCRED RAND ECVAL ECFN ECLIST ECCONTRA

%%

%public assign_rhs:
| RAND LPAREN n_expr = expr RPAREN {
  function
    | [Expr.(App (Var qual_ident, [], _)) as e], is_init
      when QualIdent.is_local qual_ident ->
      let args = e :: n_expr :: [] in
      Stmt.(Basic (StmtExt (EC_Rand is_init, args))), Some (Expr.mk_int 0)
    | e :: _, _ -> Error.syntax_error (Expr.to_loc e) "Expected single variable on left-hand side of RandVal"
    | [], _ -> assert false 
}
| RAND LPAREN n_expr = expr SEMICOLON ECVAL COLON NEQ errorVal = expr RPAREN {
  function
    | [Expr.(App (Var qual_ident, [], _)) as e], is_init
      when QualIdent.is_local qual_ident ->
      let args = e :: n_expr :: errorVal :: [] in
      Stmt.(Basic (StmtExt (EC_RandVal is_init, args))), Some (Expr.mk_int 0)
    | e :: _, _ -> Error.syntax_error (Expr.to_loc e) "Expected single variable on left-hand side of RandVal"
    | [], _ -> assert false
}
| RAND LPAREN n_expr = expr SEMICOLON ECFN COLON ERRORCRED LPAREN ec_expr = expr RPAREN COMMA x = IDENT IMPLIES fn_body = expr RPAREN {
    function
    | [Expr.(App (Var qual_ident, [], _)) as e], is_init
      when QualIdent.is_local qual_ident ->
      let args = e :: n_expr :: ec_expr :: (Expr.mk_var ~typ:Type.int (QualIdent.from_ident x)) :: fn_body :: [] in
      Stmt.(Basic (StmtExt (EC_RandFn is_init, args))), Some (Expr.mk_int 0)
    | e :: _, _ -> Error.syntax_error (Expr.to_loc e) "Expected single variable on left-hand side of RANDFN"
    | [], _ -> assert false 
}
| RAND LPAREN n_expr = expr SEMICOLON ECLIST COLON NOTIN ls_expr = expr RPAREN {
  function
    | [Expr.(App (Var qual_ident, [], _)) as e], is_init
      when QualIdent.is_local qual_ident ->
      let args = e :: n_expr :: ls_expr :: [] in
      Stmt.(Basic (StmtExt (EC_RandList is_init , args))), Some (Expr.mk_int 0)
    | e :: _, _ -> Error.syntax_error (Expr.to_loc e) "Expected single variable on left-hand side of RANDFN"
    | [], _ -> assert false 
}
;

%public stmt_ext:
| ECCONTRA; SEMICOLON { [Stmt.Basic (StmtExt (EC_Contra, []))]}

%public unary_expr:
| ERRORCRED; LPAREN e = expr RPAREN {
  Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt ErrorCreds) [e]
}
