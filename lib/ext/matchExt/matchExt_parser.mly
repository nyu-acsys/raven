%{

open Ext.MatchExtInstance

%}

%token IS MATCH DARROW

%%

(* `is` is a comparison, so it binds at exactly the level `==`/`!=` do: tighter than
   `&&`/`||`/`==>`, looser than arithmetic. That matters in practice -- a validity
   condition like `a is tokens && b is tokens && ...` (see test/comparison/tokens.rav)
   is the shape `is` exists for, and it would need parens around every single test if
   `is` bound looser than `&&`. Reaching this level from a fragment file needs
   `eq_expr` to be declared `%public` in core parser.mly, which it is (see the comment
   there); menhir's --merge_into makes only %public nonterminals referenceable from
   another fragment.
   Left operand is `rel_expr`, the level *below*, rather than `eq_expr` itself: that
   makes `is` non-associative with `==`/`!=` by construction, matching how those are
   already declared (`%nonassoc EQEQ NEQ`). Taking `eq_expr` on the left would instead
   leave `a == b is c` genuinely ambiguous -- a shift/reduce conflict menhir resolves
   arbitrarily -- for an expression nobody means to write; this way it's a clean syntax
   error, and no precedence declaration has to be shared across fragment files. *)
%public eq_expr:
| e = rel_expr; IS; c = decl_name {
    let ctor_qi = QualIdent.from_ident c in
    Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt (Is ctor_qi)) [e]
  }

(* `match` is fully bracketed (leading `MATCH` keyword, trailing `RBRACE`), so it's an
   atomic alternative rather than an infix form with a precedence to place -- it hangs
   off `unary_expr` (the tightest %public level) the same way `compr_expr`'s `{| ... |}`
   forms sit at `primary`, letting a `match` appear as an operand of anything, e.g.
   `match xs { ... } + 1`. Arms are separated the same way `data`'s own `variant_decl`
   list already is (see core parser.mly's `type_def_expr`): an optional semicolon
   between arms, relying on `CASE` itself as the unambiguous marker for where the next
   arm begins, since nothing inside an arm's own body expression can start with
   `CASE`. *)
%public unary_expr:
| MATCH; e = expr; LBRACE; arms = separated_list(option(SEMICOLON), match_arm_expr); RBRACE {
    let arm_list, bodies = List.split arms in
    Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.any (ExprExt (MatchExpr arm_list)) (e :: bodies)
  }

(* `_` is not a dedicated token -- like `import M._`'s own wildcard (see
   `import_dir` in core parser.mly), it's an ordinary `IDENT` whose name is checked
   post-hoc. *)
match_arm_expr:
| CASE; ctor = decl_name; vars = option(delimited(LPAREN, separated_list(COMMA, IDENT), RPAREN));
  DARROW; body = expr {
    let arm_vars = match vars with Some vs -> vs | None -> [] in
    let arm_ctor = if String.equal (Ident.name ctor) "_" then None else Some ctor in
    ({ arm_ctor; arm_vars }, body)
  }
(* Infix constructor pattern, `case hd :: tl => ...` -- notation for the same
   one-level match a prefix `case ::(hd, tl) => ...` arm builds; the record shape
   is identical, so nothing downstream (MatchExt's type-checking/rewriting) needs
   to know which spelling produced it. Restricted to right-associative-shaped
   names (reusing [right_assoc_binary_op_ident] from core parser.mly) rather than
   every operator tier: a constructor pattern like `case a + b => ...` has no
   idiomatic use, and reuse here avoids five unused alternatives. This does not
   enable chained/nested patterns (`case hd :: hd2 :: tl => ...`) -- arms bind one
   constructor's fields flatly, with no recursive sub-pattern structure, regardless
   of operator syntax. *)
| CASE; v1 = IDENT; ctor = right_assoc_binary_op_ident; v2 = IDENT; DARROW; body = expr {
    ({ arm_ctor = Some ctor; arm_vars = [v1; v2] }, body)
  }
