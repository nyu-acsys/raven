%{

open Ext.AssertWithExtInstance

%}

%%

(* `assert e with { proof }` -- split out of the core `with_clause` grammar rule into
   its own self-contained `stmt_ext` production (see AssertWithExt.ml's module doc
   comment) so the "only valid after `assert`" restriction, and the actual
   type-directed rewrite, live with the extension rather than in the core grammar. *)
%public stmt_ext:
| sk = SPEC; e = expr; WITH; b = block; {
  match sk with
  | Stmt.Assert ->
    let spec =
      Stmt.{ spec_form = e;
             spec_atomic = false;
             spec_comment = None;
             spec_error = [];
             spec_source = None; }
    in
    let proof : Stmt.t = { stmt_desc = b; stmt_loc = Loc.make $startpos(b) $endpos(b) } in
    [Stmt.StmtExt (AssertWith { spec; proof })]
  | _ -> Error.syntax_error (Loc.make $startpos $startpos) "A 'with' clause is only allowed in assert statements"
}
