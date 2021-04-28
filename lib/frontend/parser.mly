%{

open Util
open Ast
open Base
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
%token ASSUME ASSERT HAVOC NEW RETURN
%token IF ELSE WHILE
%token <Ast.func_kind> FUNC
%token <Ast.proc_kind> PROC
%token DATA GHOST IMPLICIT VAR VAL STRUCT TYPE
%token INTERFACE MODULE  
%token RETURNS REQUIRES ENSURES INVARIANT
%token REF INT BOOL SET MAP
%token EOF

%nonassoc COLONEQ 
%nonassoc ASSUME ASSERT
%nonassoc NEW FREE

%left SEMICOLON
%left OR AND
%right IMPLIES
%left DOT
%right NOT
%nonassoc IFF
%nonassoc LT GT LEQ GEQ
%nonassoc EQ NEQ 
%left ADDOP MINUS
%left MULTOP
%nonassoc LPAREN

%start main
%type <unit> main
%%

main:
| e = expr { e }
;

primary:
| c = CONSTVAL { Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) c []) }
| LPAREN; e = expr; RPAREN { e }
| e = set_expr { e }
| e = proc_call { e }
| e = field_access { e }
| e = field_write { e }
| e = set_expr { e }
;

set_expr:
| LBRACEPIPE; es = expr_list_opt; RBRACEPIPE {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Setenum es)
  }
| LBRACEPIPE; v = bound_var; COLONCOLON; e = expr; RBRACEPIPE {
    Expr.(mk_binder ~loc:(Loc.mk_loc $startpos $endpos) Compr [v] e)
  }
;
  
/*
alloc:
| NEW var_type { New ($2, [], Loc.mk_loc 1 2) }
| NEW var_type LPAREN expr_list_opt RPAREN { New ($2, $4, Loc.mk_loc 1 5) }
;*/

proc_call:
/*| MAP LT var_type, var_type GT LPAREN expr_list_opt RPAREN {*/
| p = IDENT; LPAREN; es = expr_list_opt; RPAREN {
  Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) (Var p) es) }
;
                                                             
ident: 
| x = IDENT {
  Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) (Var (QuantIdent.from_ident x)) []) }
;

field_access:
| id = ident; DOT; m = ident {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Dot [id; m])
  }
| e = primary; DOT; m = ident {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Dot [e; m]) }
;

field_write:
| e1 = ident; LBRACKETPIPE; e2 = expr; COLONEQ; e3 = expr; RBRACKETPIPE {
  Expr.mk_app ~loc:(Loc.mk_loc $startpos $endpos) Write [e1; e2; e3]
}
| e1 = primary; LBRACKETPIPE; e2 = expr; COLONEQ; e3 = expr; RBRACKETPIPE {
  Expr.mk_app ~loc:(Loc.mk_loc $startpos $endpos) Write [e1; e2; e3]
}
;
  
unary_expr:
| e = primary { e }
| e = ident { e }
| MINUS; e = unary_expr {
  Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Uminus [e]) }
| e = unary_expr_not_plus_minus { e }
;

unary_expr_not_plus_minus:
| NOT; e = unary_expr  { Expr.mk_app ~loc:(Loc.mk_loc $startpos $endpos) Expr.Not [e] }
;

diff_expr:
| e = unary_expr { e }
| e1 = diff_expr; DIFF; e2 = unary_expr {
  Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Diff [e1; e2])
}
;

mult_expr:
| e = diff_expr { e }
| e1 = mult_expr; op = MULTOP; e2 = diff_expr {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) op [e1; e2])
  }
;

add_op:
| op = ADDOP { op }
| MINUS { Expr.Minus }
  
add_expr:
| e = mult_expr { e }
| e1 = add_expr; op = add_op; e2 = mult_expr {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) op [e1; e2])
  }
;
  
rel_expr:
| c = comp_seq {
  match c with
  | e, [] -> e
  | _, comps -> Expr.mk_and ~loc:(Loc.mk_loc $startpos $endpos) comps
}
| e1 = rel_expr; IN; e2 = add_expr {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Elem [e1; e2])
  } 
| e1 = rel_expr; NOTIN; e2 = add_expr {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Not [mk_app ~loc:(Loc.mk_loc $startpos $endpos) Elem [e1; e2]]) 
  }
;

comp_op:
| LT { OpLt }
| GT { OpGt }
| LEQ { OpLeq }
| GEQ { OpGeq }
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
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Eq [e1; e2])
  }
| e1 = eq_expr; NEQ; e2 = eq_expr {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Not [mk_app ~loc:(Loc.mk_loc $startpos $endpos) Eq [e1; e2]])
  }
;

and_expr:
| e = eq_expr { e }
| e1 = and_expr; AND; e2 = eq_expr {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) And [e1; e2])
  }
;

or_expr:
| e = and_expr { e }
| e1 = or_expr; OR; e2 = and_expr {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Or [e1; e2])
  }
;

impl_expr:
| e = or_expr { e }
| e1 = or_expr; IMPLIES; e2 = impl_expr {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Impl [e1; e2])
  }
;

iff_expr:
| e = impl_expr { e }
| e1 = iff_expr IFF e2 = iff_expr {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Eq [e1; e2])
  }
;

ite_expr:
| e = iff_expr { e }
| e1 = ite_expr; QMARK; e2 = iff_expr; COLON; e3 = iff_expr {
    Expr.(mk_app ~loc:(Loc.mk_loc $startpos $endpos) Ite [e1; e2; e3])
  }
;
    
quant_var:
| v = bound_var { v }
;
  
bound_var:
| x = IDENT; COLON; t = type_expr {
    let decl = { v_name = x;
                 v_type = t;
                 v_ghost = false;
                 v_implicit = false;
                 v_pos = Loc.mk_loc $startpos $endpos;
                 v_scope = GrassUtil.global_scope; (* scope is fixed later *) } in
    decl
  }
;

type_expr:
| INT { Type.mk_int (Loc.mk_loc $startpos $endpos) }
| BOOL { Type.mk_bool (Loc.mk_loc $startpos $endpos) }
| x = IDENT { Type.mk_var (Loc.mk_loc $startpos $endpos) (QualIdent.from_ident x) }
| SET { Type.mk_set (Loc.mk_loc $startpos $endpos) }
| MAP { Type.mk_map (Loc.mk_loc $startpos $endpos) }
| t = type_expr; LBRACKET; ts = type_expr_list; RBRACKET { Type.mk_app ~loc:(Loc.mk_loc $startpos $endpos) t ts }
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
    Expr.(mk_binder ~loc:(Loc.mk_loc $startpos $endpos) q vs e)
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
