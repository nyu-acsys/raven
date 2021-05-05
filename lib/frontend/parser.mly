%{

open Util
open Ast
(*open Base*)
(*open Lexing*)

(*
let fix_scopes stmnt =
  let rec fs scope = function
    | LocalVars (decls, es_opt, pos) ->
        let decls1 = 
          List.map (fun decl -> { decl with v_scope = scope }) decls
        in 
        LocalVars (decls1, es_opt, pos)
    | Block (stmnts, pos) ->
        Block (List.map (fs pos) stmnts, pos)
    | If (cond, t, e, pos) ->
        If (cond, fs scope t, fs scope e, pos)
    | Choice (stmnts, pos) ->
        Choice (List.map (fs scope) stmnts, pos)
    | Loop (inv, preb, cond, postb, pos) ->
        Loop (inv, fs scope preb, cond, fs scope postb, pos)
    | stmnt -> stmnt
  in fs GrassUtil.global_scope stmnt

let fst3 (v, _, _) = v
let snd3 (_, v, _) = v
let trd3 (_, _, v) = v


type rhs_string_maybe =
  | StringRHS of string
  | NormalRHS of exprs
*)
%}

%token <Ast.Ident.t> IDENT
%token <Ast.Expr.constr> CONSTVAL
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token LBRACEPIPE RBRACEPIPE LBRACKETPIPE RBRACKETPIPE
%token COLON COLONEQ COLONCOLON SEMICOLON DOT PIPE QMARK
%token <Ast.Expr.constr> ADDOP MULTOP
%token DIFF MINUS
%token EQ NEQ LEQ GEQ LT GT IN NOTIN SUBSETEQ
%token AND OR IMPLIES IFF NOT COMMA
%token <Ast.Expr.binder> QUANT
%token ATOMIC ASSUME ASSERT HAVOC NEW RETURN
%token IF ELSE WHILE
%token <Ast.Callable.call_kind> FUNC
%token <Ast.Callable.call_kind> PROC
%token DATA GHOST IMPLICIT STRUCT TYPE
%token <bool> VAR  
%token INTERFACE MODULE  
%token RETURNS REQUIRES ENSURES INVARIANT
%token REF INT BOOL SET MAP
%token EOF


%nonassoc IFF
%nonassoc EQ NEQ 

%start main
%type <Ast.Stmt.t> main
%%

main:
| s = stmt; EOF { s }
;

(** Statements *)

stmt:
| s = stmt_desc { Stmt.{ stmt_desc = s; stmt_loc = Loc.make $startpos $endpos } }

stmt_desc:
| s = stmt_wo_trailing_substmt { s }
| s = if_then_stmt { s }
| s = if_then_else_stmt { s }
| s = while_stmt { s }
;

stmt_no_short_if:
| s = stmt_no_short_if_desc { Stmt.{ stmt_desc = s; stmt_loc = Loc.make $startpos $endpos } }
    
stmt_no_short_if_desc:
| s = stmt_wo_trailing_substmt { s }
| s = if_then_else_stmt_no_short_if  { s }
| s = while_stmt_no_short_if  { s }
;

stmt_wo_trailing_substmt:
(* variable definition *)
| g = ghost_modifier; v = VAR; decl = bound_var; SEMICOLON {
    let open Stmt in
    let decl =
      Expr.{ decl with
             var_ghost = g;
             var_const = v;
           }
    in
    Basic (VarDef { var_decl = decl; var_init = None; })
}
| g = ghost_modifier; v = VAR; decl = bound_var_opt_type; COLONEQ; e = expr; SEMICOLON {
    let open Stmt in
    let decl =
      Expr.{ decl with
             var_ghost = g;
             var_const = v;
           }
    in
    Basic (VarDef { var_decl = decl; var_init = Some e; })
}
(* nested block *)
| s = block { s }
(*
(* procedure call *)
| SEMICOLON {
  
  Assign ([], [$1], mk_position 1 1)
  }
/* assignment */
| assign_lhs_list COLONEQ expr_list_string SEMICOLON {
  let lhs = $1 in
  match $3 with
  | NormalRHS es -> Assign (lhs, es, mk_position 1 4)
  | StringRHS str ->
    assert (List.length lhs = 1);
    let lhs = List.hd lhs in
    let pos1 = mk_position 1 4 in
    let pos2 = mk_position 3 3 in
    let pos3 = mk_position 1 1 in
    let char_to_byte c =
      UnaryOp (OpToByte, IntVal(Int64.of_int (int_of_char c), pos2), pos2)
    in
    let mk_assign idx value =
      let lhs_read = Read (lhs, IntVal(Int64.of_int idx, pos3), pos3) in
      Assign([lhs_read], [value], pos1)
    in
    let rec to_list n = 
      if n >= (String.length str) then 
        let v = UnaryOp (OpToByte, IntVal(Int64.zero, pos2), pos2) in
        [mk_assign n v]
      else
        let v = char_to_byte (String.get str n) in
        let a = mk_assign n v in
        a :: (to_list (n+1))
    in
    Block (to_list 0, pos1)
}
/* havoc */
| HAVOC expr_list_opt SEMICOLON { 
  Havoc ($2, mk_position 1 3)
}
/* assume */
| contract_mods ASSUME expr SEMICOLON {
  Assume ($3, fst $1, mk_position (if $1 <> (false, false) then 1 else 2) 4)
}
/* assert */
| contract_mods ASSERT expr with_clause {
  $4 (fst $1) $3 (mk_position (if $1 <> (false, false) then 1 else 2) 4) None
}
| contract_mods ASSERT STRINGVAL expr with_clause {
  $5 (fst $1) $4 (mk_position (if $1 <> (false, false) then 1 else 2) 5) (Some $3)
  (*Assert ($3, fst $1, mk_position (if $1 <> (false, false) then 1 else 2) 4)*)
}
*)
(* return *)
| RETURN; es = expr_list_opt; SEMICOLON { 
  Stmt.(Basic (Return es))
}
;

ghost_modifier:
| GHOST { true }
| (* empty *) { false }
;


  
block:
| LBRACE; stmts = stmt_list_opt; RBRACE { Block stmts }
;

stmt_list_opt:
| s = stmt; stmts = stmt_list_opt { s :: stmts }
| (* empty *) { [] }
      
(*
assign_lhs_list:
| assign_lhs COMMA assign_lhs_list { $1 :: $3 }
| assign_lhs { [$1] }
;

assign_lhs:
| ident { $1 }
| field_access_no_set { $1 }
| array_access_no_set { $1 }
;
*)
    
if_then_stmt:
| IF; LPAREN; e = expr; RPAREN; st = stmt  {
  let cond =
    Stmt.{ cond_test = e;
           cond_then = st;
           cond_else = mk_skip (Loc.make $endpos $endpos);
         }
  in
  Stmt.(Cond cond)
}
;

if_then_else_stmt:
| IF; LPAREN; e = expr; RPAREN; st = stmt_no_short_if; ELSE; se = stmt { 
  let cond =
    Stmt.{ cond_test = e;
           cond_then = st;
           cond_else = se;
         }
  in
  Stmt.(Cond cond)
}
;

if_then_else_stmt_no_short_if:
| IF; LPAREN; e = expr; RPAREN; st = stmt_no_short_if; ELSE; se = stmt_no_short_if { 
  let cond =
    Stmt.{ cond_test = e;
           cond_then = st;
           cond_else = se;
         }
  in
  Stmt.(Cond cond)
}
;
  
while_stmt:
| WHILE; LPAREN; e = expr; RPAREN; cs = loop_contract_list; s = block {
  let loop =
    Stmt.{ loop_contract = cs;
           loop_prebody = mk_skip (Loc.make $startpos $startpos);
           loop_test = e;
           loop_postbody = { stmt_desc = s; stmt_loc = Loc.make $startpos(s) $endpos(s) };
         }
  in
  Stmt.Loop loop
}
| WHILE; LPAREN; e = expr; RPAREN; s = stmt {
  let loop =
    Stmt.{ loop_contract = [];
           loop_prebody = mk_skip (Loc.make $startpos $startpos);
           loop_test = e;
           loop_postbody = s;
         }
  in
  Stmt.Loop loop
}
;

while_stmt_no_short_if:
| WHILE; LPAREN; e = expr; RPAREN; s = stmt_no_short_if {
  let loop =
    Stmt.{ loop_contract = [];
           loop_prebody = mk_skip (Loc.make $startpos $startpos);
           loop_test = e;
           loop_postbody = s;
         }
  in
  Stmt.Loop loop
} 
;

loop_contract_list:
| loop_contract loop_contract_list { $1 :: $2 }
| loop_contract { [$1] }
;

loop_contract:
| INVARIANT; e = expr {
  let spec =
    Stmt.{ spec_form = e;
           spec_atomic = false;
           spec_name = "invariant";
           spec_error = None;
         }
  in
  spec
}
;



(** Expressions *)

primary:
| c = CONSTVAL { Expr.(mk_app ~loc:(Loc.make $startpos $endpos) c []) }
| LPAREN; e = expr; RPAREN { e }
| e = set_expr { e }
| e = dot_expr { e }
;

set_expr:
| LBRACEPIPE; es = expr_list_opt; RBRACEPIPE {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Setenum es)
  }
| LBRACEPIPE; v = bound_var; COLONCOLON; e = expr; RBRACEPIPE {
    Expr.(mk_binder ~loc:(Loc.make $startpos $endpos) Compr [v] e)
  }
;
  
(*
alloc:
| NEW var_type { New ($2, [], Loc.make 1 2) }
| NEW var_type LPAREN expr_list_opt RPAREN { New ($2, $4, Loc.make 1 5) }
;*)

dot_expr:
(*| MAP LT var_type, var_type GT LPAREN expr_list_opt RPAREN {*)
| p = qual_ident_expr; co = call_opt {
  Base.Option.map co ~f:(fun (c, es) ->
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) c (p :: es)))
  |> Base.Option.value ~default:p
}
;

call_opt:
| LPAREN; es = expr_list_opt; RPAREN { Some (Expr.Call, es) }
| LBRACKETPIPE; e2 = expr; COLONEQ; e3 = expr; RBRACKETPIPE {
  Some (Write, [e2; e3])
}
| (* empty *) { None }
  
qual_ident_expr:
| x = ident { x }
| p = primary DOT x = ident {
  Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Dot [p; x])
}
                                                              
ident: 
| x = IDENT {
  Expr.(mk_app ~loc:(Loc.make $startpos $endpos) (Var (QualIdent.from_ident x)) []) }
;
  
unary_expr:
| e = primary { e }
(*| e = ident { e }*)
| MINUS; e = unary_expr {
  Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Uminus [e]) }
| e = unary_expr_not_plus_minus { e }
;

unary_expr_not_plus_minus:
| NOT; e = unary_expr  { Expr.mk_app ~loc:(Loc.make $startpos $endpos) Expr.Not [e] }
;

diff_expr:
| e = unary_expr { e }
| e1 = diff_expr; DIFF; e2 = unary_expr {
  Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Diff [e1; e2])
}
;

mult_expr:
| e = diff_expr { e }
| e1 = mult_expr; op = MULTOP; e2 = diff_expr {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) op [e1; e2])
  }
;

add_op:
| op = ADDOP { op }
| MINUS { Expr.Minus }
  
add_expr:
| e = mult_expr { e }
| e1 = add_expr; op = add_op; e2 = mult_expr {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) op [e1; e2])
  }
;
  
rel_expr:
| c = comp_seq {
  match c with
  | e, [] -> e
  | _, comps -> Expr.mk_and ~loc:(Loc.make $startpos $endpos) comps
}
| e1 = rel_expr; IN; e2 = add_expr {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Elem [e1; e2])
  } 
| e1 = rel_expr; NOTIN; e2 = add_expr {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Not [mk_app ~loc:(Loc.make $startpos $endpos) Elem [e1; e2]]) 
  }
;

comp_op:
| LT { Lt }
| GT { Gt }
| LEQ { Leq }
| GEQ { Geq }
| SUBSETEQ { Subseteq }
;

comp_seq:
| e = add_expr { (e, []) }
| e1 = add_expr; op = comp_op; cseq = comp_seq {
  let e2, comps = cseq in
  let loc1 = Expr.loc e1 in
  let loc2 = Expr.loc e2 in
  (e1, Expr.(mk_app ~loc:(Loc.merge loc1 loc2) op [e1; e2]) :: comps)
}
;
  
eq_expr:
| e = rel_expr { e }
| e1 = eq_expr; EQ; e2 = eq_expr {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Eq [e1; e2])
  }
| e1 = eq_expr; NEQ; e2 = eq_expr {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Not [mk_app ~loc:(Loc.make $startpos $endpos) Eq [e1; e2]])
  }
;

and_expr:
| e = eq_expr { e }
| e1 = and_expr; AND; e2 = eq_expr {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) And [e1; e2])
  }
;

or_expr:
| e = and_expr { e }
| e1 = or_expr; OR; e2 = and_expr {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Or [e1; e2])
  }
;

impl_expr:
| e = or_expr { e }
| e1 = or_expr; IMPLIES; e2 = impl_expr {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Impl [e1; e2])
  }
;

iff_expr:
| e = impl_expr { e }
| e1 = iff_expr IFF e2 = iff_expr {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Eq [e1; e2])
  }
;

ite_expr:
| e = iff_expr { e }
| e1 = ite_expr; QMARK; e2 = iff_expr; COLON; e3 = iff_expr {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Ite [e1; e2; e3])
  }
;
    
quant_var:
| v = bound_var { v }
;

bound_var:
| x = IDENT; COLON; t = type_expr {
    let decl =
      Expr.{ var_name = x;
             var_type = t;
             var_loc = Loc.make $startpos $endpos;
             var_const = true;
             var_ghost = false;
             var_implicit = false;
           }
    in
    decl
  }
;

bound_var_opt_type:
| x = IDENT { 
  let decl =
    Expr.{ var_name = x;
           var_type = Type.Any;
           var_loc = Loc.make $startpos $endpos;
           var_const = true;
           var_ghost = false;
           var_implicit = false;
         }
  in
  decl
} 
;

   
type_expr:
| INT { Type.mk_int (Loc.make $startpos $endpos) }
| BOOL { Type.mk_bool (Loc.make $startpos $endpos) }
| x = IDENT { Type.mk_var (Loc.make $startpos $endpos) (QualIdent.from_ident x) }
| SET { Type.mk_set (Loc.make $startpos $endpos) }
| MAP { Type.mk_map (Loc.make $startpos $endpos) }
| t = type_expr; LBRACKET; ts = type_expr_list; RBRACKET { Type.mk_app ~loc:(Loc.make $startpos $endpos) t ts }
;

type_expr_list:
| t = type_expr; COMMA; ts = type_expr_list { t :: ts }
| t = type_expr { [t] }
;
    
quant_var_list:
| COMMA; v = quant_var; vs = quant_var_list { v :: vs }
| /* empty */ { [] }
;

quant_vars:
| v = quant_var; vs = quant_var_list { v :: vs }
;

quant_expr: 
| e = ite_expr { e }
| q = QUANT; vs = quant_vars; COLONCOLON; e = quant_expr {
    Expr.(mk_binder ~loc:(Loc.make $startpos $endpos) q vs e)
  }
;

expr:
| e = quant_expr { e } 
;

expr_list_opt:
| es = expr_list { es }
| /* empty */ { [] }
;

expr_list:
| e = expr; COMMA; es = expr_list { e :: es }
| e = expr { [e] }
;
