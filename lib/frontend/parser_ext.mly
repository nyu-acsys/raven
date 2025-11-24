%{

open Ext.Ext

%}

%token CAS FAA XCHG

%start assignExt

%%
assignExt: 
| f = atomicExt { f }

atomicExt:
| CAS LPAREN cas_ref = qual_ident DOT cas_fld = qual_ident COMMA cas_old_val = expr COMMA cas_new_val = expr RPAREN {
  function
    | [Expr.(App (Var qual_ident, [], _)) as e], atomic_inbuilt_is_init
      when QualIdent.is_local qual_ident ->
        let args = e :: cas_fld :: cas_ref :: [cas_old_val; cas_new_val]
        in begin
        match atomic_inbuilt_is_init with
        | true -> 
            Stmt.(Basic (StmtExt (AtomicInbuiltInit Cas, args))), Some (Expr.mk_bool true)
        | false -> Stmt.(Basic (StmtExt (AtomicInbuiltNonInit Cas, args))), Some (Expr.mk_bool true)
        end
    | e :: _, _ -> Error.syntax_error (Expr.to_loc e) "Expected single field location or local variables on left-hand side of cas"
    | [], _ -> assert false
}
| FAA LPAREN faa_ref = qual_ident DOT faa_fld = qual_ident COMMA faa_val = expr RPAREN {
  function
    | [Expr.(App (Var qual_ident, [], _)) as e], atomic_inbuilt_is_init
      when QualIdent.is_local qual_ident ->
        let args = e :: faa_fld :: faa_ref :: [faa_val]
        in begin
        match atomic_inbuilt_is_init with
        | true -> 
            Stmt.(Basic (StmtExt (AtomicInbuiltInit Faa, args))), Some (Expr.mk_int 0)
        | false -> 
            Stmt.(Basic (StmtExt (AtomicInbuiltNonInit Faa, args))), Some (Expr.mk_int 0)
        end
    | e :: _, _ -> Error.syntax_error (Expr.to_loc e) "Expected single field location or local variables on left-hand side of faa"
    | [], _ -> assert false
}
| XCHG LPAREN xchg_ref = qual_ident DOT xchg_fld = qual_ident COMMA xchg_new_val = expr RPAREN {
  function
    | [Expr.(App (Var qual_ident, [], _)) as e], atomic_inbuilt_is_init
      when QualIdent.is_local qual_ident ->
        let args = e :: xchg_fld :: xchg_ref :: [xchg_new_val]
        in begin
        match atomic_inbuilt_is_init with
        | true ->
            Stmt.(Basic (StmtExt (AtomicInbuiltInit Xchg, args))), Some (xchg_new_val)
        | false ->
            Stmt.(Basic (StmtExt (AtomicInbuiltNonInit Xchg, args))), Some (xchg_new_val)
        end
    | e :: _, _ -> Error.syntax_error (Expr.to_loc e) "Expected single field location or local variables on left-hand side of faa"
    | [], _ -> assert false
}