%{

open Util
open Ast
(*open Base*)


%}

%token <Ast.Ident.t> IDENT MODIDENT
%token <Ast.Expr.constr> CONSTVAL
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token LBRACEPIPE RBRACEPIPE LBRACKETPIPE RBRACKETPIPE LGHOSTBRACE RGHOSTBRACE
%token COLON COLONEQ COLONCOLON SEMICOLON DOT QMARK
%token <Ast.Expr.constr> ADDOP MULTOP
%token DIFF MINUS
%token EQ EQEQ NEQ LEQ GEQ LT GT IN NOTIN SUBSETEQ
%token AND OR IMPLIES IFF NOT COMMA
%token <Ast.Expr.binder> QUANT
%token <Ast.Stmt.spec_kind> SPEC
%token <Ast.Stmt.use_kind> USE  
%token HAVOC NEW RETURN OWN
%token IF ELSE WHILE
%token <Ast.Callable.call_kind> FUNC
%token <Ast.Callable.call_kind> PROC
%token CASE DATA INT REAL BOOL PERM SET MAP ATOMICTOKEN FIELD REF
%token ATOMIC GHOST IMPLICIT REP  
%token <bool> VAR  
%token INTERFACE MODULE TYPE IMPORT
%token RETURNS REQUIRES ENSURES INVARIANT
%token EOF


%nonassoc IFF
%nonassoc EQEQ NEQ 

%start main
%type <Ast.Module.t0> main
/* %type <Ast.Type.t> type_def_expr
%type <Ast.Type.t> type_expr */
%%

main:
| ms = member_def_list_opt; EOF {
  let open Module in
  let decl =
    { empty_decl with
      mod_decl_name = Ident.make "$Program" 0;
    }
  in
  { mod_decl = decl;
    mod_def = ms;
    mod_interface = false;
  }
}
;

(** Member Definitions *)

module_def:
| MODULE; decl = module_header; def = module_alias_or_impl {
  let open Module in
  match def with
  | ModImpl impl ->
      ModImpl { impl with mod_decl = decl; }
  | ModAlias ma ->
  (* //TODO: Figure out what is happening here *)
      if decl.mod_decl_formals <> [] then
        Error.syntax_error (Loc.make $startpos(def) $startpos(def)) (Some "Expected {")
      else
        ModAlias { ma with
                   mod_alias_name = decl.mod_decl_name;
                   mod_alias_loc = decl.mod_decl_loc }
}
  
module_alias_or_impl:
| LBRACE; ms = member_def_list_opt; RBRACE {
  Module.( ModImpl { mod_decl = empty_decl;
                     mod_def = ms;
                     mod_interface = false;
                   } )
}
| EQ; t = type_expr {
  Module.( ModAlias { mod_alias_name = Ident.make "" 0;
                      mod_alias_type = Type.mk_bot Loc.dummy;
                      mod_alias_def = Some t;
                      mod_alias_loc = Loc.dummy;
                    } )
}

member_def_list_opt:
| m = member_def; ms = member_def_list_opt { m :: ms }
| m = member_def; SEMICOLON; ms = member_def_list_opt { m :: ms }
| (* empty *) { [] }

member_def:
| def = field_def {Module.FieldDef def}
| def = module_def { Module.ModDef def }
| def = interface_def { Module.ModDef def }
| def = type_def { Module.TypeAlias def }
| def = var_def { Module.ValDef def }
| def = proc_def 
| def = func_def { Module.CallDef def }
| imp = import_dir { Module.Import imp }
  
field_def:
| FIELD x = IDENT; COLON; t = type_expr {
    let decl =
      Module.{ field_name = x;
      field_type = t;
      field_loc = Loc.make $startpos $endpos
           }
    in
    decl
  }

type_def:
| def = type_decl; EQ; t = type_def_expr {
  let open Module in
  { def with type_alias_def = Some t }
}

type_def_expr:
| t = type_expr { t }
| DATA; LBRACE; decls = separated_list(SEMICOLON, variant_decl) RBRACE {
  Type.mk_data decls (Loc.make $startpos $endpos)
}

variant_decl:
| CASE; id = IDENT args = option(variant_args) {
  let args = Base.Option.value args ~default:[] in
  Type.{ variant_name = id;
         variant_loc = Loc.make $startpos(id) $endpos(id);
         variant_args = args;
       }
}

variant_args:
| LPAREN; args = separated_list(COMMA, bound_var); RPAREN { args }

    
proc_def:
| def = proc_decl; s = block {
  let open Callable in
  let body =
    Stmt.{ stmt_desc = s; stmt_loc = Loc.make $startpos(s) $endpos(s) }
  in 
  match def with
  | ProcDef def ->
      ProcDef { def with proc_body = Some body }
  | _ -> assert false
}

func_def:
| def = func_decl; LBRACE body = expr RBRACE {
  let open Callable in
  match def with
  | FuncDef def ->
      FuncDef { def with func_body = Some body }
  | _ -> assert false
}

    

(** Member Declarations *)

interface_def:
| INTERFACE; decl = module_header; LBRACE ms = list(member_decl) RBRACE {
  Module.( ModImpl { mod_decl = { decl with mod_decl_loc = Loc.make $startpos $endpos };
                     mod_def = ms;
                     mod_interface = true;
                   } )
}
    
module_header:
| id = MODIDENT; pdecls = module_param_list_opt; rts = return_type_list_opt {
  let open Module in
  let add m id ma =
    match Base.Map.add m ~key:id ~data:ma with
    | `Ok m1 -> m1
    | `Duplicate -> Error.redeclaration_error ma.mod_alias_loc (Ident.name id)
  in
  let formals, mod_aliases =
    List.fold_left (fun (formals, mod_aliases) ma ->
      ma.mod_alias_name :: formals, add mod_aliases ma.mod_alias_name ma)
      ([], Base.Map.empty (module Ident)) pdecls 
  in
  let formals = List.rev formals in
  let decl =
    { empty_decl with
      mod_decl_name = id;
      mod_decl_formals = formals;
      mod_decl_returns = rts;
      mod_decl_mod_aliases = mod_aliases;
      mod_decl_loc = Loc.make $startpos(id) $endpos(id);
    }
  in
  decl
}

module_decl:
| MODULE; id = MODIDENT; COLON; t = type_expr; tdef = module_alias_def_opt {
  Module.( ModAlias { mod_alias_name = id;
                      mod_alias_type = t;
                      mod_alias_def = tdef;
                      mod_alias_loc = Loc.make $startpos(id) $endpos(id);
                    } )
}
| MODULE; id = MODIDENT; tdef = module_alias_def {
  Module.( ModAlias { mod_alias_name = id;
                      mod_alias_type = Type.mk_bot Loc.dummy;
                      mod_alias_def = tdef;
                      mod_alias_loc = Loc.make $startpos(id) $endpos(id);
                    } )
}

module_alias_def_opt:
| t = module_alias_def { t }
| (* empty *) { None }

module_alias_def:
| EQ; t = type_expr { Some t }
    
return_type_list_opt:
| COLON; ts = separated_nonempty_list(COMMA, type_expr) { ts }
| (* empty *) { [] }

    
module_param_list_opt:
| LBRACKET ps = separated_list(COMMA, module_param) RBRACKET { ps }
| (* empty *) { [] }
  
module_param:
| id = MODIDENT; COLON; t = type_expr {
  let decl =
    Module.{ mod_alias_name = id;
             mod_alias_type = t;
             mod_alias_def = None;
             mod_alias_loc = Loc.make $startpos $endpos;
           }
  in
  decl
}

member_decl:
| def = type_decl { Module.TypeAlias def }
| def = interface_def { Module.ModDef def }
| def = module_decl { Module.ModDef def }
| def = var_decl { Module.ValDef def }
| def = proc_decl 
| def = func_decl { Module.CallDef def }
| imp = import_dir { Module.Import imp }
    
    
import_dir:
| IMPORT; t = type_expr { Module.ModImport t }
    
type_decl:
| m = type_mod; TYPE; id = MODIDENT {
  let ta =
    Module.{ type_alias_name = id;
             type_alias_def = None;
             type_alias_rep = m;
             type_alias_loc = Loc.make $startpos $endpos }
  in
  ta
}


 
type_mod:
| REP { true }
| (* empty *) { false }
;

proc_decl:
| k = PROC; decl = callable_decl {
  Callable.( ProcDef { proc_decl = { decl with call_decl_kind = k }; proc_body = None } )
}

func_decl:
| k = FUNC; decl = callable_decl {
  Callable.( FuncDef { func_decl = { decl with call_decl_kind = k }; func_body = None } )
}

callable_decl:
  id = IDENT; LPAREN; pdecls = var_decls_with_modifiers; RPAREN; rdecls = return_params; cs = contracts {
  let add m id decl =
    match Base.Map.add m ~key:id ~data:decl with
    | `Ok m1 -> m1
    | `Duplicate -> Error.redeclaration_error decl.Type.var_loc (Ident.name id)
  in
  let formals, locals =
    List.fold_left (fun (formals, locals) decl ->
      Type.(decl.var_name :: formals, add locals decl.var_name decl))
      ([], Base.Map.empty (module Ident)) pdecls 
  in
  let returns, locals =
    List.fold_left (fun (outputs, locals) decl ->
      Type.(decl.var_name :: outputs, add locals decl.var_name decl))
      ([], locals) rdecls
  in
  let precond, postcond = cs in
  let decl =
    Callable.{ call_decl_kind = Func;
               call_decl_name = id;
               call_decl_formals = List.rev formals;
               call_decl_returns = List.rev returns;
               call_decl_locals = locals;
               call_decl_precond = precond;
               call_decl_postcond = postcond;
               call_decl_loc = Loc.make $startpos(id) $endpos(id);
             }
  in decl
}

return_params:
| RETURNS; LPAREN; decls = var_decls_with_modifiers; RPAREN { decls }
| (* empty *) { [] }
   
var_decls_with_modifiers:
| var_decl_with_modifiers var_decl_with_modifiers_list { $1 :: $2 }
| /* empty */ { [] }
;

var_decl_with_modifiers_list:
| COMMA var_decl_with_modifiers var_decl_with_modifiers_list { $2 :: $3 }
| /* empty */ { [] }
;

var_decl_with_modifiers:
| m = var_modifier; decl = bound_var {
  let ghost, implicit = m in
  let decl =
    Type.{ decl with
           var_ghost = ghost;
           var_implicit = implicit;
         }
  in
  decl
}
;

contracts:
| c = contract; cs = contracts { (fst c @ fst cs, snd c @ snd cs) }
| /* empty */ { [], [] }
;

contract:
| m = contract_mods; REQUIRES; e = expr {
  let spec =
    Stmt.{ spec_form = e;
           spec_atomic = m;
           spec_error = None;
         }
  in
  ([spec], [])
}
| m = contract_mods; ENSURES; e = expr {
  let spec =
    Stmt.{ spec_form = e;
           spec_atomic = m;
           spec_error = None;
         }
  in
  ([], [spec])
}
;

contract_mods:
| ATOMIC { true }
| (* empty *) { false }
;
  
(** Statements *)

stmt:
| s = stmt_desc { Stmt.{ stmt_desc = s; stmt_loc = Loc.make $startpos $endpos } }

stmt_desc:
| s = stmt_wo_trailing_substmt { s }
| s = if_then_stmt { s }
| s = if_then_else_stmt { s }
| s = while_stmt { s }
| s = ghost_block { s }
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
| def = var_decl; SEMICOLON {
    Basic (VarDef def)
}
| def = var_def; SEMICOLON {
    Basic (VarDef def)
}
(* nested block *)
| s = block { s }
(* procedure call *)
| e = call_expr; SEMICOLON {
  let assign =
    Stmt.{ assign_lhs = [];
           assign_rhs = e;
         }
  in
  Stmt.(Basic (Assign assign))
}
(* assignment / allocation *)
| es = separated_nonempty_list(COMMA, expr); COLONEQ; e = new_or_expr; SEMICOLON {
  let open Stmt in
  match e with
  | Basic (New new_descr) ->
      (match es with
      | [Expr.App(Expr.Var x, _, _)] -> Basic (New { new_descr with new_lhs = x })
      | _ -> Error.syntax_error (Loc.make $startpos(es) $endpos(es)) (Some "Result of allocation must be assigned to a single variable"))
  | Basic (Assign assign) ->
      Basic (Assign { assign with assign_lhs = es })
  | _ -> assert false
}
(* havoc *)
| HAVOC; es = separated_nonempty_list(COMMA, expr); SEMICOLON { 
  Stmt.(Basic (Havoc es))
}

(* assume / assert / inhale / exhale *)
| sk = SPEC; e = expr; SEMICOLON {
  let open Stmt in
  let spec = { spec_form = e;
               spec_atomic = false;
               spec_error = None; }
  in
  Basic (Spec (sk, spec))
}
(*| contract_mods ASSERT expr with_clause {
  $4 (fst $1) $3 (mk_position (if $1 <> (false, false) then 1 else 2) 4) None
}
| contract_mods ASSERT STRINGVAL expr with_clause {
  $5 (fst $1) $4 (mk_position (if $1 <> (false, false) then 1 else 2) 5) (Some $3)
  (*Assert ($3, fst $1, mk_position (if $1 <> (false, false) then 1 else 2) 4)*)
}
*)
(* return *)
| RETURN; es = separated_list(COMMA, expr); SEMICOLON {
  let e = match es with
  | [e] -> e
  | es -> Expr.mk_tuple ~loc:(Loc.make $startpos(es) $endpos(es)) es
  in
  Stmt.(Basic (Return e))
}
(* unfold / fold / openInv / closeInv *)
| use_kind = USE; id = qual_ident; LPAREN; es = separated_list(COMMA, expr); RPAREN; SEMICOLON {
  Stmt.(Basic (Use {use_kind = use_kind; use_name = Expr.to_qual_ident id; use_args = es}))
}
;

new_or_expr:
| NEW LPAREN fes = separated_list(COMMA, pair(qual_ident, option(preceded(COLON, expr)))) RPAREN {
  let new_descr = Stmt.{
    new_lhs = QualIdent.from_ident (Ident.make "" 0);
    new_args = List.map (fun (f, e_opt) -> (Expr.to_qual_ident f, e_opt)) fes;
  }
  in
  Stmt.(Basic (New new_descr))
}
| e = expr {
  let assign =
    Stmt.{ assign_lhs = [];
           assign_rhs = e;
         }
  in
  Stmt.(Basic (Assign assign))
}

  
var_decl:
| g = ghost_modifier; v = VAR; decl = bound_var {
  let decl =
    Type.{ decl with
           var_ghost = g;
           var_const = v;
         }
  in
  Stmt.{ var_decl = decl; var_init = None }
}

var_def:
| g = ghost_modifier; v = VAR; decl = bound_var_opt_type; EQ; e = expr {
  let decl =
    Type.{ decl with
           var_ghost = g;
           var_const = v;
         }
  in
  Stmt.{ var_decl = decl; var_init = Some e }
}
| g = ghost_modifier; v = VAR; decl = bound_var_opt_type; COLONEQ; e = expr {
  let decl =
    Type.{ decl with
           var_ghost = g;
           var_const = v;
         }
  in
  Stmt.{ var_decl = decl; var_init = Some e }
}
    
ghost_modifier:
| GHOST { true }
| (* empty *) { false }
;

var_modifier:
| IMPLICIT; GHOST { true, true }
| g = ghost_modifier { false, g }
; 

  
block:
| LBRACE; stmts = stmt_list_opt; RBRACE { Stmt.mk_block stmts }
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
           spec_error = None;
         }
  in
  spec
}
;

ghost_block:
| LGHOSTBRACE; stmts = stmt_list_opt; RGHOSTBRACE {
  Stmt.mk_block ~ghost:true stmts
}
;
(** Expressions *)

primary:
| c = CONSTVAL { Expr.(mk_app ~loc:(Loc.make $startpos $endpos) c []) }
| LPAREN; e = expr; RPAREN { e }
| e = compr_expr { e }
| e = dot_expr { e }
| e = own_expr { e }
| e = maplookup_expr { e }
;

compr_expr:
| LBRACEPIPE; es = separated_list(COMMA, expr); RBRACEPIPE {
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Setenum es)
  }
| LBRACEPIPE; v = bound_var; COLONCOLON; e = expr; RBRACEPIPE {
    Expr.(mk_binder ~loc:(Loc.make $startpos $endpos) ~typ:Type.(mk_set (Loc.make $startpos $endpos) bot) Compr [v] e)
  }
| LBRACKETPIPE; v = bound_var; COLONCOLON; e = expr; RBRACKETPIPE {
    Expr.(mk_binder ~loc:(Loc.make $startpos $endpos) ~typ:Type.(mk_map (Loc.make $startpos $endpos) any bot) Compr [v] e)
  }
;
  
dot_expr:
(*| MAP LT var_type, var_type GT LPAREN expr_list_opt RPAREN {*)
| p = qual_ident_expr; co = call_opt {
  Base.Option.map co ~f:(fun (c, es) ->
    let constr, args =
      let p_ident = Expr.to_qual_ident p in
      Base.Option.map c ~f:(fun c -> c, p :: es) |> 
      Base.Option.value ~default:(Expr.Call (p_ident, Loc.make $startpos(p) $endpos(p)), es)
    in
    Expr.(mk_app ~loc:(Loc.make $startpos $endpos) constr args))
  |> Base.Option.value ~default:p
}
;

own_expr:
| OWN; LPAREN; es = expr_list; RPAREN {
  Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Own es)
}

maplookup_expr:
| e1 = qual_ident_expr; LBRACKET; e2 = expr; RBRACKET {
  Expr.(mk_app ~loc:(Loc.make $startpos $endpos) MapLookUp [e1; e2])

}

call_expr:
| p = qual_ident_expr; ces = call {
  let _, es = ces in
  Expr.(mk_app ~loc:(Loc.make $startpos $endpos) (Call (Expr.to_qual_ident p, Loc.make $startpos(p) $endpos(p))) es)
}
  
call:
| LPAREN; es = separated_list(COMMA, expr); RPAREN { (None, es) }
  
call_opt:
| c = call { Some c }
| LBRACKET; e2 = expr; COLONEQ; e3 = expr; RBRACKET {
  Some (Some MapUpdate, [e2; e3])
}
| (* empty *) { None }
  
qual_ident_expr:
| x = qual_ident { x }
| p = primary DOT x = qual_ident {
  Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Read [p; x])
}
| p = primary DOT LPAREN x = qual_ident RPAREN {
  Expr.(mk_app ~loc:(Loc.make $startpos $endpos) Read [p; x])
}

qual_ident:
| x = ident { x }
| m = mod_ident; DOT; x = IDENT {
  Expr.(mk_app ~loc:(Loc.make $startpos $endpos) (Var (QualIdent.append m x)) [])
}
    
mod_ident:
| x = MODIDENT { QualIdent.from_ident x}
| x = mod_ident; DOT; y = MODIDENT { QualIdent.append x y}

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
| e1 = eq_expr; EQEQ; e2 = eq_expr {
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
      Type.{ var_name = x;
             var_type = t;
             var_loc = Loc.make $startpos $endpos;
             var_const = false;
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
    Type.{ var_name = x;
           var_type = Type.mk_bot Loc.dummy;
           var_loc = Loc.make $startpos $endpos;
           var_const = true;
           var_ghost = false;
           var_implicit = false;
         }
  in
  decl
}
| x = IDENT; COLON; t = type_expr {
  let decl =
    Type.{ var_name = x;
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

type_expr:
| INT { Type.mk_int (Loc.make $startpos $endpos) }
| REAL { Type.mk_real (Loc.make $startpos $endpos)}
| BOOL { Type.mk_bool (Loc.make $startpos $endpos) }
| REF { Type.mk_ref (Loc.make $startpos $endpos) }
| PERM { Type.mk_perm (Loc.make $startpos $endpos)}
| ATOMICTOKEN { Type.mk_atomic_token (Loc.make $startpos $endpos) }
//| x = IDENT { Type.mk_var (Loc.make $startpos $endpos) (QualIdent.from_ident x) }
| SET LBRACKET t = type_expr RBRACKET { Type.mk_set (Loc.make $startpos $endpos) t }
| MAP LBRACKET; t1 = type_expr; COMMA; t2 = type_expr; RBRACKET { Type.mk_map (Loc.make $startpos $endpos) t1 t2 }
| x = mod_ident { Type.mk_var (Loc.make $startpos $endpos) x }
| LPAREN ts = type_expr_list RPAREN { Type.(App(Prod, ts, Type.mk_attr (Loc.make $startpos $endpos))) }
| x = mod_ident LBRACKET; ts = type_expr_list; RBRACKET {
  Type.(App(Var x, ts, Type.mk_attr (Loc.make $startpos $endpos))) }
    
  
type_expr_list:
| ts = separated_nonempty_list(COMMA, type_expr) { ts }
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

expr_list:
| e = expr; COMMA; es = expr_list { e :: es }
| e = expr { [e] }
;
