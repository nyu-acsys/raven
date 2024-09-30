%{

open Util
open Ast
(*open Base*)

%}

%token <Ast.Ident.t> IDENT MODIDENT
%token <Ast.Expr.constr> CONSTVAL
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token LBRACEPIPE RBRACEPIPE LBRACKETPIPE RBRACKETPIPE LGHOSTBRACE RGHOSTBRACE
%token COLON COLONEQ COLONCOLON SEMICOLON DOT QMARK COLONPIPE
%token <Ast.Expr.constr> ADDOP MULTOP
%token DIFF MINUS
%token EQ EQEQ NEQ LEQ GEQ LT GT IN NOTIN SUBSETEQ
%token <Int64.t> HASH
%token AND OR IMPLIES IFF NOT COMMA
%token <Ast.Expr.binder> QUANT
%token <Ast.Stmt.spec_kind> SPEC
%token <Ast.Stmt.use_kind> USE  
%token HAVOC NEW RETURN OWN AU
%token IF ELSE WHILE CAS
%token <Ast.Callable.call_kind> FUNC
%token PROC AXIOM LEMMA
%token CASE DATA INT REAL BOOL PERM SET MAP ATOMICTOKEN FIELD REF
%token ATOMIC GHOST IMPLICIT REP AUTO WITH
%token <bool> VAR
%token <bool> MODULE
%token <string> STRINGVAL
%token TYPE IMPORT INCLUDE
%token RETURNS REQUIRES ENSURES INVARIANT
%token EOF


%nonassoc IFF
%nonassoc EQEQ NEQ 

%start main
%type <string list * Ast.Module.t> main
/* %type <Ast.Type.t> type_def_expr
%type <Ast.Type.t> type_expr */
%%

main:
| files = includes; ms = member_def_list_opt; EOF {
  let open Module in
  let decl =
    { empty_decl with
      mod_decl_name = Ident.make (Loc.make $startpos(ms) $endpos(ms)) "$Program" 0;
    }
  in
  files,
  { mod_decl = decl;
    mod_def = ms;
  }
}
;

includes:
| INCLUDE s = STRINGVAL; files = includes { s :: files }
| /* empty */ { [] }

(** Member Definitions *)

module_def:
| is_interface = MODULE; decl = module_header; def = module_inst_or_impl_or_decl {
  let open Module in
  match def with
  | ModDef impl ->
      ModDef { impl with mod_decl = { decl with mod_decl_is_interface = is_interface } }
  | ModInst ma ->
  (* //TODO: Figure out what is happening here *)
      if decl.mod_decl_formals <> [] then
        Error.syntax_error (Loc.make $startpos(def) $startpos(def)) ("Expected {")
      else
        let mod_inst_type =
          match decl.mod_decl_returns, ma.mod_inst_def with
        | Some mod_inst_type, _ 
        | None, Some (mod_inst_type, _) -> mod_inst_type
        | None, None ->
            Error.syntax_error (Loc.make $endpos(decl) $endpos(decl))
              ("Expected specification of interface implemented by this module")
        in
        ModInst { ma with
                  mod_inst_type;
                  mod_inst_name = decl.mod_decl_name;
                  mod_inst_is_interface = is_interface;
                  mod_inst_loc = decl.mod_decl_loc }
  | symbol -> symbol
}
  
module_header:
| id = MODIDENT; mod_formals = module_param_list_opt; rt = return_type_opt {
  let open Module in
  let decl =
    { empty_decl with
      mod_decl_name = id;
      mod_decl_formals = mod_formals;
      mod_decl_returns = rt;
      mod_decl_loc = Loc.make $startpos(id) $endpos(id);
    }
  in
  decl
}

return_type_opt:
| COLON; t = mod_ident { Some t }
| (* empty *) { None }

module_inst_or_impl_or_decl:
| LBRACE; ms = member_def_list_opt; RBRACE {
  Module.( ModDef { mod_decl = empty_decl;
                    mod_def = ms;
                  } )
}
| EQ; mod_name = mod_ident; args = mod_inst_args {
  Module.( ModInst { mod_inst_name = Ident.make Loc.dummy "" 0; (* dummy *)
                     mod_inst_type = QualIdent.make [] (Ident.make Loc.dummy "" 0); (* dummy *)
                     mod_inst_def = Some (mod_name, args);
                     mod_inst_is_interface = false;
                     mod_inst_loc = Loc.dummy;
                   } )
}
| (* empty *) {
  Module.( ModInst { mod_inst_name = Ident.make Loc.dummy "" 0; (* dummy *)
                     mod_inst_type = QualIdent.make [] (Ident.make Loc.dummy "" 0); (* dummy *)
                     mod_inst_def = None;
                     mod_inst_is_interface = false;
                     mod_inst_loc = Loc.dummy;
                   } )
}

mod_inst_args:
| LBRACKET ids = separated_list(COMMA, mod_ident) RBRACKET { ids }
| { [] }
    
member_def_list_opt:
| m = member_def; ms = member_def_list_opt {
  match m with
  | Module.SymbolDef (VarDef { var_decl = { var_loc = loc; var_const = false; _}; _ }) ->
      Error.syntax_error loc "Modules and interfaces cannot have var members"
  | _ -> m :: ms
}
| m = member_def; SEMICOLON; ms = member_def_list_opt { m :: ms }
| (* empty *) { [] }

member_def:
| def = field_def { Module.SymbolDef (Module.FieldDef def)}
| def = module_def { Module.SymbolDef def }
/*| def = interface_def { Module.SymbolDef def }*/
| def = type_def { Module.SymbolDef (Module.TypeDef def) }
| def = var_def { Module.SymbolDef (Module.VarDef def) }
| def = proc_def 
| def = func_def {Module.SymbolDef (Module.CallDef def) }
| imp = import_dir { Module.Import imp }
  
field_def:
| g = ghost_modifier; FIELD x = IDENT; COLON; t = type_expr {
    let decl =
      Module.{ field_name = x;
               field_type = Type.mk_fld (Loc.make $startpos(t) $endpos(t)) t;
               field_is_ghost = g;
               field_loc = Loc.make $startpos $endpos
           }
    in
    decl
  }

type_def:
| def = type_decl; t = option(preceded(EQ, type_def_expr)) {
  let open Module in
  { def with type_def_expr = t }
}

type_def_expr:
| t = type_expr { t }
| DATA; LBRACE; decls = separated_list(option(SEMICOLON), variant_decl) RBRACE {
  Type.mk_data (QualIdent.from_ident (Ident.make Loc.dummy "" 0)) decls (Loc.make $startpos $endpos)
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
| k = proc_kind; def = proc_decl; body = option(block) {
  let open Callable in
  let call_decl_kind, is_axiom, call_decl_is_auto = k in
  let _  =
    match is_axiom, body with
    | true, Some _ ->
        let loc = Loc.make $startpos(body) $endpos(body) in
        Error.syntax_error loc "Axiom declarations cannot have bodies. Did you mean to declare a lemma?"
    | _ -> () 
  in
  let def = { def with call_decl = { def.call_decl with call_decl_kind; call_decl_is_auto } } in
  let proc_body = Option.map body ~f:(fun s ->
    Stmt.{ stmt_desc = s; stmt_loc = Loc.make $startpos(body) $endpos(body) })
  in
  { def with call_def = ProcDef { proc_body } }
}

proc_kind:
| PROC { (Callable.Proc, false, false) }
| is_auto = option(AUTO); LEMMA { (Callable.Lemma, false, is_auto <> None) }
| is_auto = option(AUTO); AXIOM { (Callable.Lemma, true, is_auto <> None) }
    
func_def:
| def = func_decl; body = option(delimited(LBRACE, expr, RBRACE)) {
  let open Callable in
  { def with call_def = FuncDef { func_body = body } }
}

    

(** Member Declarations *)
   
module_param_list_opt:
| LBRACKET ps = separated_list(COMMA, module_param) RBRACKET { ps }
| (* empty *) { [] }
  
module_param:
| id = MODIDENT; COLON; t = mod_ident {
  let decl =
    Module.{ mod_inst_name = id;
             mod_inst_type = t;
             mod_inst_def = None;
             mod_inst_is_interface = false;
             mod_inst_loc = Loc.make $startpos $endpos;
           }
  in
  decl
}

import_dir:
| IMPORT; id = qual_ident {
  let ident = Expr.to_qual_ident id in
  let import_all =
    ident |> QualIdent.unqualify |> Ident.name |> String.equal "_"
  in
  let import_name =
    if import_all then QualIdent.pop ident else ident
  in
  { import_name; import_all; import_loc = Loc.make $startpos $endpos }
}
| IMPORT; id = mod_ident { { import_name = id; import_all = false; import_loc = Loc.make $startpos $endpos } }
    
type_decl:
| m = type_mod; TYPE; id = MODIDENT {
  let ta =
    Module.{ type_def_name = id;
             type_def_expr = None;
             type_def_rep = m;
             type_def_loc = Loc.make $startpos $endpos }
  in
  ta
}


 
type_mod:
| REP { true }
| (* empty *) { false }
;

proc_decl:
| decl = callable_decl {
  Callable.{ call_decl = { decl with call_decl_kind = Proc }; call_def = ProcDef { proc_body = None } }
}

func_decl:
| k = FUNC; decl = callable_decl {
  Callable.{ call_decl = { decl with call_decl_kind = k }; call_def = FuncDef { func_body = None } }
}
| k = FUNC; decl = callable_decl_out_vars {
  Callable.{ call_decl = { decl with call_decl_kind = k }; call_def = ProcDef { proc_body = None } }
}

callable_decl:
  id = IDENT; LPAREN; formals = var_decls_with_modifiers; RPAREN; returns = return_params; cs = contracts {
  let precond, postcond = cs in
  let decl =
    Callable.{ call_decl_kind = Func;
               call_decl_name = id;
               call_decl_formals = formals;
               call_decl_returns = returns;
               call_decl_locals = [];
               call_decl_precond = precond;
               call_decl_postcond = postcond;
               call_decl_is_free = false;
               call_decl_is_auto = false;
               call_decl_mask = None;
               call_decl_loc = Loc.make $startpos(id) $endpos(id);
             }
  in decl
}

callable_decl_out_vars:
  id = IDENT; LPAREN; formals = var_decls_with_modifiers; SEMICOLON; returns = var_decls_with_modifiers; RPAREN; cs = contracts {
  let precond, postcond = cs in
  let decl =
    Callable.{ call_decl_kind = Func;
               call_decl_name = id;
               call_decl_formals = formals;
               call_decl_returns = returns;
               call_decl_locals = [];
               call_decl_precond = precond;
               call_decl_postcond = postcond;
               call_decl_is_free = false;
               call_decl_is_auto = false;
               call_decl_mask = None;
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
           spec_comment = None;
           spec_error = [];
         }
  in
  ([spec], [])
}
| m = contract_mods; ENSURES; e = expr {
  let spec =
    Stmt.{ spec_form = e;
           spec_atomic = m;
           spec_comment = None;
           spec_error = [];
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
           assign_is_init = false;
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
      | _ -> Error.syntax_error (Loc.make $startpos(es) $endpos(es)) ("Result of allocation must be assigned to a single variable"))
  | Basic (Assign assign) ->
      Basic (Assign { assign with assign_lhs = es })
  | _ -> assert false
}
(* bind *)
| es = separated_nonempty_list(COMMA, expr); COLONPIPE; e = expr; SEMICOLON {
  let bind =
    Stmt.{ bind_lhs = es;
           bind_rhs = e;
         }
  in
  Stmt.(Basic (Bind bind))
}
(* havoc *)
| HAVOC; id = qual_ident; SEMICOLON { 
  Stmt.(Basic (Havoc (Expr.to_qual_ident id)))
}

(* assume / assert / inhale / exhale *)
| sk = SPEC; e = expr; mk_spec = with_clause {
  mk_spec sk e
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

with_clause:
| SEMICOLON { 
  fun sk e ->
    let open Stmt in
    let spec = { spec_form = e;
                 spec_atomic = false;
                 spec_comment = None;
                 spec_error = []; }
    in
    Basic (Spec (sk, spec))
}
| WITH b = block; {
  let open Stmt in
  function
    | Assert -> fun e ->
        let vs, e1 = match e with
        | Expr.Binder (Expr.Forall, vs, _, e1, _) ->
            vs, e1
        | _ -> [], e
        in
        let loc : location = Expr.to_loc e in
        let nondet_var =
          Type.{ var_name = Ident.fresh loc "$nondet";
                 var_loc = loc; 
                 var_type = Type.bool;
                 var_const = true;
                 var_ghost = true;
                 var_implicit = false; }
        in

        let nondet_var_def = VarDef {var_decl = nondet_var; var_init = None} in

        let checks =
          let assert_stmt = Stmt.mk_assert_expr ~loc:(Expr.to_loc e1) e1 in
          let assume_false = Stmt.mk_assume_expr ~loc (Expr.mk_bool ~loc false) in
          List.map (fun decl -> { stmt_desc = Basic (VarDef { var_decl = decl; var_init = None }); stmt_loc = decl.var_loc } ) vs @
          [{ stmt_desc = b; stmt_loc = Loc.make $startpos(b) $endpos(b) }; assert_stmt; assume_false]
        in
        let assume_e = Stmt.mk_assume_expr ~loc e in
        let cond_stmt =
          Cond {
            cond_test = Some (Expr.from_var_decl nondet_var);
            cond_then = assume_e;
            cond_else = (Stmt.mk_block_stmt ~loc checks);
            cond_if_assumes_false = false;
        }
        in
        mk_block [{ stmt_desc = Basic nondet_var_def; stmt_loc = loc }; { stmt_desc = cond_stmt; stmt_loc = loc}]
    | _ -> Error.syntax_error (Loc.make $startpos $startpos) "A 'with' clause is only allowed in assert statements"
}
  
new_or_expr:
| NEW LPAREN fes = separated_list(COMMA, pair(qual_ident, option(preceded(COLON, expr)))) RPAREN {
  let new_descr = Stmt.{
    new_lhs = QualIdent.from_ident (Ident.make Loc.dummy "" 0);
    new_args = List.map (fun (f, e_opt) -> (Expr.to_qual_ident f, e_opt)) fes;
  }
  in
  Stmt.(Basic (New new_descr))
}
| e = expr {
  let assign =
    Stmt.{ assign_lhs = [];
           assign_rhs = e;
           assign_is_init = false
         }
  in
  Stmt.(Basic (Assign assign))
}
 
var_def:
| g = ghost_modifier; v = VAR; decl = bound_var_opt_type; e = option(preceded(EQ, expr)) {
  let decl =
    Type.{ decl with
           var_ghost = g;
           var_const = v;
         }
  in
  Stmt.{ var_decl = decl; var_init = e }
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
    Stmt.{ cond_test = Some e;
           cond_then = st;
           cond_else = mk_skip ~loc:(Loc.make $endpos $endpos);
           cond_if_assumes_false = false;
         }
  in
  Stmt.(Cond cond)
}
;

if_then_else_stmt:
| IF; LPAREN; e = expr; RPAREN; st = stmt_no_short_if; ELSE; se = stmt { 
  let cond =
    Stmt.{ cond_test = Some e;
           cond_then = st;
           cond_else = se;
           cond_if_assumes_false = false;
         }
  in
  Stmt.(Cond cond)
}
;

if_then_else_stmt_no_short_if:
| IF; LPAREN; e = expr; RPAREN; st = stmt_no_short_if; ELSE; se = stmt_no_short_if { 
  let cond =
    Stmt.{ cond_test = Some e;
           cond_then = st;
           cond_else = se;
           cond_if_assumes_false = false;
         }
  in
  Stmt.(Cond cond)
}
;
  
while_stmt:
| WHILE; LPAREN; e = expr; RPAREN; cs = loop_contract_list; s = block {
  let loop =
    Stmt.{ loop_contract = cs;
           loop_prebody = mk_skip ~loc:(Loc.make $startpos $startpos);
           loop_test = e;
           loop_postbody = { stmt_desc = s; stmt_loc = Loc.make $startpos(s) $endpos(s) };
         }
  in
  Stmt.Loop loop
}
| WHILE; LPAREN; e = expr; RPAREN; s = stmt {
  let loop =
    Stmt.{ loop_contract = [];
           loop_prebody = mk_skip ~loc:(Loc.make $startpos $startpos);
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
           loop_prebody = mk_skip ~loc:(Loc.make $startpos $startpos);
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
  (*let loc = Expr.to_loc e in
  let msg caller =
    Error.Verification,
    loc,
    if caller = proc_name then
      "This loop invariant may not hold on loop entry"
    else 
      "This loop invariant may not be maintained by the loop"
  in*)
  let spec =
    Stmt.{ spec_form = e;
           spec_atomic = false;
           spec_comment = None;
           spec_error = [];
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
| c = CONSTVAL { Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) c []) }
| LPAREN; e = expr; RPAREN cont = map_update_opt { cont e }
| e = compr_expr { e }
| e = dot_expr { e }
| e = own_expr { e }
| e = cas_expr { e }
| e = au_expr { e }
| e = lookup_expr { e }
;

compr_expr:
| LBRACEPIPE; es = separated_list(COMMA, expr); RBRACEPIPE {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Setenum es)
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
| p = qual_ident_expr; co = call_opt { co p }
;

own_expr:
| OWN; LPAREN; es = expr_list; RPAREN {
  Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Own es)
}

cas_expr:
| CAS; LPAREN; es = expr_list; RPAREN {
  Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Cas es)
}

au_expr:
| AU; LPAREN; c = qual_ident; es = expr_list; RPAREN {
  Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) (AUPred (Expr.to_qual_ident c)) es)
}

lookup_expr:
| e1 = qual_ident_expr; e_fn = lookup; { e_fn e1 }
| LPAREN; e1 = expr; RPAREN; e_fn = lookup; { e_fn e1 }

lookup:
| LBRACKET; e2 = expr; RBRACKET {
  fun e1 -> Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) MapLookUp [e1; e2])
}     
| n = HASH {
  let e2 = Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos(n) $endpos(n)) (Expr.Int n) []) in
  fun e1 -> Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) TupleLookUp [e1; e2])
}
    
call_expr:
| p = qual_ident_expr; es = call {
  Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) (Expr.Var (Expr.to_qual_ident p)) es)
}
  
call:
| LPAREN; es = separated_list(COMMA, expr); RPAREN { es }
  
call_opt:
| es = call; cont = map_update_opt {
  fun p ->
    let p_ident = Expr.to_qual_ident p in
    let e =
      Expr.(mk_app ~typ:Type.bot ~loc:(Loc.merge (to_loc p) (Loc.make $startpos $endpos)) (Var p_ident) es)
    in
    cont e
}
| cont = map_update_opt { cont }

map_update_opt:
| LBRACKET; e2 = expr; COLONEQ; e3 = expr; RBRACKET cont = map_update_opt {
  fun e ->
    let e_upd =
      Expr.(mk_app ~typ:Type.bot ~loc:(Loc.merge (to_loc e) (Loc.make $startpos $endpos)) MapUpdate [e; e2; e3])
    in
    cont e_upd
}
| (* empty *) { fun p -> p }
  
qual_ident_expr:
| x = qual_ident { x }
| p = primary DOT x = qual_ident {
  Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Read [p; x])
}
| p = primary DOT LPAREN x = qual_ident RPAREN {
  Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Read [p; x])
}

qual_ident:
| x = ident { x }
| m = mod_ident; DOT; x = IDENT {
  Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) (Var (QualIdent.append m x)) [])
}
 
mod_ident:
| x = MODIDENT { QualIdent.from_ident x}
| x = mod_ident; DOT; y = MODIDENT { QualIdent.append x y}

ident: 
| x = IDENT {
  Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) (Var (QualIdent.from_ident x)) []) }
;
  
unary_expr:
| e = primary { e }
(*| e = ident { e }*)
| MINUS; e = unary_expr {
  Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Uminus [e]) }
| e = unary_expr_not_plus_minus { e }
;

unary_expr_not_plus_minus:
| NOT; e = unary_expr  { Expr.mk_app ~loc:(Loc.make $startpos $endpos) ~typ:Type.bot Expr.Not [e] }
;

diff_expr:
| e = unary_expr { e }
| e1 = diff_expr; DIFF; e2 = unary_expr {
  Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Diff [e1; e2])
}
;

mult_expr:
| e = diff_expr { e }
| e1 = mult_expr; op = MULTOP; e2 = diff_expr {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) op [e1; e2])
  }
;

add_op:
| op = ADDOP { op }
| MINUS { Expr.Minus }
  
add_expr:
| e = mult_expr { e }
| e1 = add_expr; op = add_op; e2 = mult_expr {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) op [e1; e2])
  }
;
  
rel_expr:
| c = comp_seq {
  match c with
  | e, [] -> e
  | _, comps -> Base.List.reduce_exn comps ~f:(fun e1 e2 -> Expr.mk_and ~loc:(Loc.merge (Expr.to_loc e1) (Expr.to_loc e2)) [e1; e2])
}
| e1 = rel_expr; IN; e2 = add_expr {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Elem [e1; e2])
  } 
| e1 = rel_expr; NOTIN; e2 = add_expr {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Not [mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Elem [e1; e2]]) 
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
  let loc1 = Expr.to_loc e1 in
  let loc2 = Expr.to_loc e2 in
  (e1, Expr.(mk_app ~typ:Type.bot ~loc:(Loc.merge loc1 loc2) op [e1; e2]) :: comps)
}
;
  
eq_expr:
| e = rel_expr { e }
| e1 = eq_expr; EQEQ; e2 = eq_expr {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Eq [e1; e2])
  }
| e1 = eq_expr; NEQ; e2 = eq_expr {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Not [mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Eq [e1; e2]])
  }
;

and_expr:
| e = eq_expr { e }
| e1 = and_expr; AND; e2 = eq_expr {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) And [e1; e2])
  }
;

or_expr:
| e = and_expr { e }
| e1 = or_expr; OR; e2 = and_expr {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Or [e1; e2])
  }
;



impl_expr:
| e = or_expr { e }
| e1 = or_expr; IMPLIES; e2 = impl_expr {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Impl [e1; e2])
  }
;

iff_expr:
| e = impl_expr { e }
| e1 = iff_expr IFF e2 = iff_expr {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Eq [e1; e2])
  }
;

ite_expr:
| e = iff_expr { e }
| e1 = ite_expr; QMARK; e2 = iff_expr; COLON; e3 = iff_expr {
    Expr.(mk_app ~typ:Type.bot ~loc:(Loc.make $startpos $endpos) Ite [e1; e2; e3])
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
| LPAREN ts = type_expr_list RPAREN { Type.mk_prod (Loc.make $startpos $endpos) ts }
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
| q = QUANT; vs = quant_vars; COLONCOLON; trigs = patterns; e = quant_expr {
    Expr.(mk_binder ~loc:(Loc.make $startpos $endpos) ~trigs q vs e)
  }
;

patterns:
| LBRACE; es = expr_list; RBRACE; trgs = patterns { es :: trgs }
| /* empty */ { [] }

expr:
| e = quant_expr { e } 
| LPAREN; e = expr; COMMA; es = expr_list; RPAREN { Expr.mk_tuple ~loc:(Loc.make $startpos $endpos) (e :: es) }
;

expr_list:
| e = expr; COMMA; es = expr_list { e :: es }
| e = expr { [e] }
;
