%{

open Ext.ProphecyExtInstance

%}

%token PROPH RESOLVE PROPHPRED

%%

(* `Proph[T]` is a multi-shot prophecy (predicts an unbounded sequence of `T`
   values); `Proph[T, 1]` is one-shot (predicts a single `T` value, resolvable at
   most once). The literal `1` is the only value accepted for the second argument
   today -- reusing `CONSTVAL` here (rather than adding a dedicated token) keeps the
   grammar surface minimal, matching how other extension fragments splice `expr`/
   literal tokens into their own productions instead of inventing new syntax
   categories. *)
%public type_expr:
| PROPH LBRACKET t=type_expr RBRACKET {
  Type.mk_app ~loc:(Loc.make $startpos $endpos) (TypeExt (ProphId false)) [t]
}
| PROPH LBRACKET t=type_expr COMMA n=CONSTVAL RBRACKET {
  match n with
  | Expr.Int 1L -> Type.mk_app ~loc:(Loc.make $startpos $endpos) (TypeExt (ProphId true)) [t]
  | _ -> Error.syntax_error (Loc.make $startpos $endpos) "Proph[T, n] only supports n = 1 (one-shot); omit the second argument for a multi-shot prophecy"
}

%public unary_expr:
| PROPH DOT PROPHPRED; LPAREN; e1=expr; COMMA; e2=expr; RPAREN {
  (* `false` is a placeholder; type-checking replaces it once it knows, from `e1`'s
     `Proph[...]` type, whether this is the one-shot or multi-shot resource. *)
  Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt (ProphResource false)) [e1; e2]
}

%public assign_rhs:
| NEW PROPH LBRACKET t=type_expr RBRACKET {
  function
  | [proph_id; proph_val], _ ->
    Stmt.(Basic (BasicStmtExt ((NewProph (false, t)), [proph_id; proph_val]))), None
  | _, _ ->
    Error.syntax_error (Type.to_loc t) "Expected a prophecy id variable and a prophecy value variable on the left-hand side of new Proph[...]"
}
| NEW PROPH LBRACKET t=type_expr COMMA n=CONSTVAL RBRACKET {
  function
  | [proph_id; proph_val], _ ->
    begin match n with
    | Expr.Int 1L ->
      Stmt.(Basic (BasicStmtExt ((NewProph (true, t)), [proph_id; proph_val]))), None
    | _ ->
      Error.syntax_error (Type.to_loc t) "new Proph[T, n] only supports n = 1 (one-shot); omit the second argument for a multi-shot prophecy"
    end
  | _, _ ->
    Error.syntax_error (Type.to_loc t) "Expected a prophecy id variable and a prophecy value variable on the left-hand side of new Proph[...]"
}

%public stmt_ext:
| PROPH DOT RESOLVE; LPAREN; e1=expr; COMMA; e2=expr; RPAREN SEMICOLON {
  (* `false` is a placeholder; see the comment on `ProphResource` above. *)
  [Stmt.Basic (BasicStmtExt (ResolveProph false, [e1; e2]))]
}
