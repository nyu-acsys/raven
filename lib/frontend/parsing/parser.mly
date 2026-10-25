%{

open Util
open Ast
(*open Base*)

(* A mixfix expression becomes a call; a pattern can spell that call explicitly. *)
let mixfix_application loc name base bounds arguments =
  match arguments with
  | None -> Surface.Expr.mixfix ~loc name base bounds
  | Some args ->
      let loc = Loc.merge (Expr.to_loc base) loc in
      let name = Ident.make loc name 0 in
      let is_hole = function
        | Expr.App (Var qi, [], _) -> QualIdent.is_local qi && Ident.name (QualIdent.unqualify qi) = "_"
        | _ -> false
      in
      let target =
        match base with
        | Expr.App (Var qi, [], _) when Ident.name (QualIdent.unqualify qi) = "_"
                                      && List.for_all is_hole bounds ->
            if QualIdent.is_local qi then QualIdent.from_ident name
            else QualIdent.append (QualIdent.pop qi) name
        | _ -> Error.syntax_error loc "Expected an operator pattern before this argument list"
      in
      Surface.Expr.call ~loc target args

(* An enumeration delimiter, and whether it is written with a pipe. *)
let checked_enumeration_name loc (opener, opener_piped) (closer, closer_piped) ~singleton =
  if not (String.equal (Expr.enumeration_closer opener) closer)
     || not (Bool.equal opener_piped closer_piped) then
    Error.syntax_error loc "Mismatched enumeration delimiter";
  Ident.make loc (Expr.enumeration_name opener ~singleton) 0

let is_enumeration_hole = function
  | Expr.App (Var qi, [], _) ->
      QualIdent.is_local qi && Ident.name (QualIdent.unqualify qi) = "_"
  | _ -> false

let check_set_comprehension loc (opener, opener_piped) (closer, closer_piped) =
  if not (String.equal opener "{" && String.equal closer "}"
          && Bool.equal opener_piped closer_piped) then
    Error.syntax_error loc "This delimiter cannot form a set comprehension"

(* The operator a MULTOP or ADDOP token stands for. *)
let binop_of_constr : Expr.constr -> Surface.Expr.binop = function
  | Mult -> Mult
  | Div -> Div
  | Mod -> Mod
  | Plus -> Plus
  | Minus -> Minus
  | _ -> assert false

(* A callable has at most one `opens` clause. *)
let single_opens_clause = function
  | [] -> None
  | [ (loc, entries) ] -> Some Callable.{ opens_entries = entries; opens_loc = loc }
  | _ :: (loc, _) :: _ ->
      Error.syntax_error loc "A callable may have at most one opens clause"

(* Checks that `inline`, if given, is applied to a function or predicate. *)
let inline_modifier ~loc (kind : Callable.call_kind) (is_inline : bool) : bool =
  match kind with
  | Invariant when is_inline -> Error.syntax_error loc "An invariant cannot be inline"
  | _ -> is_inline

%}

%token <Ast.Ident.t> IDENT MODIDENT
%token <Ast.Expr.constr> CONSTVAL
%token <Ast.Type.constr> CONSTTYPE
%token <Ast.Type.constr * int> TYPECONSTR
%token UNDERSCORE UNION INTER DIFF DOTDOT
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token LBRACEPIPE RBRACEPIPE LBRACKETPIPE RBRACKETPIPE LGHOSTBRACE RGHOSTBRACE
(* The braces of an enumeration literal written without pipes, told apart from a block's
   by the lexer. *)
%token LENUMBRACE RENUMBRACE
%token <string> ENUM_OPEN ENUM_CLOSE
%token COLON COLONGT COLONEQ COLONCOLON SEMICOLON DOT QMARK COLONPIPE
%token <Ast.Expr.constr> ADDOP MULTOP
%token MINUS
(* User-declarable symbolic operators the lexer couldn't match against
   Terminals.operator_table -- see lexer.mll's fallback classification. One
   token per precedence tier; `right_assoc_binary_op_ident` below is also where
   `::` itself lands. *)
%token <Ast.Ident.t> MULTOPSYM ADDOPSYM RABINOPSYM RELOPSYM EQOPSYM ANDOPSYM OROPSYM
%token EQ EQEQ NEQ LEQ GEQ LT GT IN NOTIN SUBSETEQ
%token <Int64.t> HASH
%token AND OR IMPLIES IFF NOT COMMA
%token <Ast.Expr.binder> QUANT
%token <Ast.Stmt.spec_kind> SPEC
%token <Ast.Stmt.use_kind> USE  
%token HAVOC NEW RETURN OWN AU AUCOMMIT CHOOSE
%token IF ELSE WHILE SPAWN
%token <Ast.Callable.call_kind> FUNC
%token PROC AXIOM LEMMA FREE
%token CASE DATA ATOMICTOKEN FIELD WHERE
(* [ATOMIC_PROC] is the modifier before [PROC]; both retain separate source spans. *)
%token ATOMIC ATOMIC_PROC GHOST IMPLICIT REP AUTO INLINE WITH CHECKED
%token <bool> VAR
%token <bool> MODULE
%token <string> STRINGVAL
%token TYPE IMPORT INCLUDE
%token RETURNS REQUIRES ENSURES INVARIANT OPENS
%token EOF

%nonassoc IFF
(* EQOPSYM joins EQEQ/NEQ's group: eq_expr is written bidirectionally recursive
   (both operands recurse into eq_expr, not just the left), so without this a
   user `=`/`!`-leading operator would be ambiguous with `==`/`!=` on chaining
   the same way `a == b == c` already is -- this declaration is what makes both
   non-chainable instead. *)
%nonassoc EQEQ NEQ EQOPSYM

%start main
%type <(string * Loc.t) list * Ast.Module.t> main
%%

main:
| files = includes; ms = member_def_list_opt; EOF {
  files, Surface.Module.program ~loc:(Loc.make $startpos(ms) $endpos(ms)) ms
}
;

includes:
| INCLUDE s = STRINGVAL; files = includes { (s, Loc.make $startpos(s) $endpos(s)) :: files }
| /* empty */ { [] }

(** Member Definitions *)

module_def:
| is_interface = MODULE; decl = module_header; def = module_inst_or_impl_or_decl {
  let open Module in
  match def with
  | ModDef impl -> Surface.Module.module_def ~interface:is_interface decl impl.mod_def
  | ModInst ma ->
      if not (Module.is_structure decl) then
        Error.syntax_error (Loc.make $startpos(def) $startpos(def))
          "A module with parameters cannot be defined with '=' (module instantiation syntax); give it a body in '{ ... }' instead"
      else if decl.mod_decl_is_sealed && Option.is_none ma.mod_inst_def then
        Error.syntax_error (Loc.make $startpos(decl) $endpos(decl))
          (Printf.sprintf !"Module %{Ident} has no definition, so it cannot be sealed with ':>'"
             decl.mod_decl_name)
      else if ma.mod_inst_is_checked && List.is_empty decl.mod_decl_returns then
        Error.syntax_error decl.mod_decl_loc
          "A checked module view must name its interface"
      else
        let mod_inst_type =
          (* A module *instance* stands for exactly one interface: [mod_inst_type]
             is a single unparameterised name. Listing several parents, or
             applying one, is only meaningful for a module *definition*. *)
          match decl.mod_decl_returns, ma.mod_inst_def with
        | [ (_, (_ :: _)) ], _ ->
            Error.syntax_error (Loc.make $startpos(decl) $endpos(decl))
              (Printf.sprintf !"Module %{Ident} has no body, so the interface it stands for cannot take arguments"
                 decl.mod_decl_name)
        | _ :: _ :: _, _ ->
            Error.syntax_error (Loc.make $startpos(decl) $endpos(decl))
              (Printf.sprintf !"Module %{Ident} has no body, so it can name at most one interface"
                 decl.mod_decl_name)
        | [ (mod_inst_type, []) ], _ -> mod_inst_type
        | [], Some application -> Module.application_target application
        | [], None ->
            Error.syntax_error (Loc.make $endpos(decl) $endpos(decl))
              (Printf.sprintf !"Module %{Ident} has no body and no interface: write 'module %{Ident} : I' naming the interface it stands for"
                 decl.mod_decl_name decl.mod_decl_name)
        in
        Surface.Module.binding ~loc:decl.mod_decl_loc ?definition:ma.mod_inst_def
          ~interface:is_interface ~sealed:decl.mod_decl_is_sealed ~checked:ma.mod_inst_is_checked decl.mod_decl_name
          mod_inst_type
  | symbol -> symbol
}
  
module_header:
| id = MODIDENT; parameters = module_param_list_opt; rt = return_type_opt {
  Surface.Module.header_with_parameters ~loc:(Loc.make $startpos(id) $endpos(id)) ~parameters
    ~implements:(fst rt) ~sealed:(snd rt) id
}

(* Interfaces implemented by this module, and whether it is sealed. Several may
   be listed, and each may be a functor application: `module M[A: I] : Base[A],
   Other`. A sealed module (`:>`) names exactly one. *)
return_type_opt:
| COLON; ts = separated_nonempty_list(COMMA, parent_spec) { (ts, false) }
| COLONGT; t = parent_spec { ([ t ], true) }
| (* empty *) { ([], false) }

parent_spec:
(* [mod_inst_args] already admits the empty case, so this covers both `Base` and
   `Base[A]`. *)
| t = mod_ident; args = mod_inst_args { (t, args) }

module_inst_or_impl_or_decl:
| LBRACE; ms = member_def_list_opt; RBRACE {
  Module.( ModDef { mod_decl = empty_decl;
                    mod_def = ms;
                  } )
}
| EQ; CHECKED; target = mod_ident {
  Module.ModInst
    (Module.mk_mod_binding ~name:(Ident.make Loc.dummy "" 0)
       ~typ:(QualIdent.make [] (Ident.make Loc.dummy "" 0))
       ~definition:(Module.Alias target) ~checked:true ~loc:Loc.dummy ())
}
| EQ; mod_name = mod_ident; application = module_application_suffix {
  Module.( ModInst (mk_mod_binding ~name:(Ident.make Loc.dummy "" 0) (* dummy *)
                     ~typ:(QualIdent.make [] (Ident.make Loc.dummy "" 0)) (* dummy *)
                     ~definition:(application mod_name) ~loc:Loc.dummy ()) )
}
| (* empty *) {
  Module.( ModInst (mk_mod_inst ~name:(Ident.make Loc.dummy "" 0) (* dummy *)
                     ~typ:(QualIdent.make [] (Ident.make Loc.dummy "" 0)) (* dummy *)
                     ~loc:Loc.dummy ()) )
}

module_application_suffix:
| LPAREN RPAREN { fun target -> Module.ApplyUnit target }
| LBRACKET tps = separated_list(COMMA, type_expr) RBRACKET {
    fun target -> Module.Apply (target, List.map Surface.Module.arg tps)
}
| { fun target -> Module.Alias target }

mod_inst_args:
| LBRACKET tps = separated_list(COMMA, type_expr) RBRACKET { List.map Surface.Module.arg tps }
| { [] }
    
member_def_list_opt:
| m = member_def_maybe_free; ms = member_def_list_opt { Surface.Module.expand_sealed m @ ms }
| (* empty *) { [] }

member_def_maybe_free:
| is_free = free symbol = member_def { Surface.Module.symbol ~free:is_free symbol }
| imp = import_dir { Surface.Module.import_member imp }

member_def:
| def = field_def { Module.FieldDef def }
| def = module_def { def }
| def = type_def { Module.TypeDef def }
| def = var_def { Module.VarDef def }
| def = proc_def 
| def = func_def { Module.CallDef def }
  
%inline free:
| FREE { true }
| { false }

field_def:
| g = ghost_modifier; FIELD x = plain_ident; COLON; t = type_expr;
  where = option(preceded(WHERE, qual_ident)) {
    Surface.Module.field ~loc:(Loc.make $symbolstartpos $endpos) ~ghost:g
      ?where:(Option.map where ~f:Expr.to_qual_ident)
      ~type_loc:(Loc.make $startpos(t) $endpos(t)) x t
  }
(* Manifest field: `field f = M.g` denotes an existing field rather than
   declaring a new one, the counterpart of `rep type T = Int` for types. The
   type and ghost-ness are taken from the target and checked in Typing. *)
| g = ghost_modifier; FIELD x = plain_ident; EQ; target = qual_ident {
    Surface.Module.field_alias ~loc:(Loc.make $symbolstartpos $endpos) ~ghost:g
      ~type_loc:(Loc.make $startpos(target) $endpos(target)) x (Expr.to_qual_ident target)
  }

type_def:
| def = type_decl; t = option(preceded(EQ, type_def_expr)) {
  let open Module in
  { def with type_def_expr = t }
}

type_def_expr:
| t = type_expr { t }
| DATA; LBRACE; decls = separated_list(option(SEMICOLON), variant_decl) RBRACE {
  Surface.Type.data ~loc:(Loc.make $symbolstartpos $endpos) decls
}

variant_decl:
| CASE; id = decl_name args = option(variant_args) {
  Surface.Type.variant ~loc:(Loc.make $startpos(id) $endpos(id)) id
    (Base.Option.value args ~default:[])
}

variant_args:
| LPAREN; args = separated_list(COMMA, bound_var); RPAREN { args }

    
proc_def:
| ka = proc_kind; def = proc_decl; body = option(block) {
  let k, atomic = ka in
  (match k, body with
   | Surface.Callable.Axiom _, Some _ ->
       let loc = Loc.make $startpos(body) $endpos(body) in
       Error.syntax_error loc "Axiom declarations cannot have bodies. Did you mean to declare a lemma?"
   | _ -> ());
  let proc_body = Option.map body ~f:(Surface.Stmt.at ~loc:(Loc.make $startpos(body) $endpos(body))) in
  Surface.Callable.proc ~atomic k def.Callable.call_decl proc_body
}

proc_kind:
| PROC { (Surface.Callable.Proc, false) }
| ATOMIC_PROC; PROC { (Surface.Callable.Proc, true) }
| is_auto = ioption(AUTO); LEMMA { (Surface.Callable.Lemma { is_auto = is_auto <> None }, false) }
| is_auto = ioption(AUTO); AXIOM { (Surface.Callable.Axiom { is_auto = is_auto <> None }, false) }
    
func_def:
| def = func_decl; EQ; target = qual_ident {
  let call_decl = { def.Callable.call_decl with call_decl_alias = Some (Expr.to_qual_ident target) } in
  Surface.Callable.func call_decl None
}
| def = func_decl; body = option(delimited(LBRACE, expr, RBRACE)) {
  Surface.Callable.func def.Callable.call_decl body
}

    

(** Member Declarations *)
   
module_param_list_opt:
| LBRACKET ps = separated_list(COMMA, module_param) RBRACKET { Module.parameters_of_formals ps }
| LPAREN RPAREN { Module.UnitParameter }
| (* empty *) { Module.Structure }
  
module_param:
| id = MODIDENT; COLON; t = mod_ident {
  Surface.Module.param ~loc:(Loc.make $symbolstartpos $endpos) id t
}

import_dir:
| IMPORT; m = mod_ident; DOT; name = mixfix_name {
  Surface.Module.import ~loc:(Loc.make $symbolstartpos $endpos) (QualIdent.append m name)
}
| IMPORT; id = qual_ident {
  let ident = Expr.to_qual_ident id in
  let import_all =
    ident |> QualIdent.unqualify |> Ident.name |> String.equal "_"
  in
  let import_name =
    if import_all then QualIdent.pop ident else ident
  in
  Surface.Module.import ~loc:(Loc.make $symbolstartpos $endpos) ~all:import_all import_name
}
| IMPORT; id = mod_ident { Surface.Module.import ~loc:(Loc.make $symbolstartpos $endpos) id }
    
type_decl:
| m = type_mod; TYPE; id = MODIDENT {
  Surface.Module.type_def ~loc:(Loc.make $symbolstartpos $endpos) ~rep:m id None
}


 
%inline type_mod:
| REP { true }
| (* empty *) { false }
;

proc_decl:
| decl = callable_decl {
  Callable.{ call_decl = { decl with call_decl_kind = Proc }; call_def = ProcDef { proc_body = None } }
}

func_decl:
| is_inline = func_modifiers; k = FUNC; decl = callable_decl {
  let loc = Loc.make $startpos(k) $endpos(k) in
  Callable.{ call_decl = { decl with call_decl_kind = k;
                                     call_decl_is_inline = inline_modifier ~loc k is_inline };
             call_def = FuncDef { func_body = None } }
}
| is_inline = func_modifiers; k = FUNC; decl = callable_decl_out_vars {
  let loc = Loc.make $startpos(k) $endpos(k) in
  Callable.{ call_decl = { decl with call_decl_kind = k;
                                     call_decl_is_inline = inline_modifier ~loc k is_inline };
             call_def = FuncDef { func_body = None } }
}

(* Whether a function or predicate is declared `inline`. `auto` is accepted here only to
   point to `inline`, which is what it used to mean for a predicate. *)
%inline func_modifiers:
| (* empty *) { false }
| INLINE { true }
| AUTO | INLINE; AUTO {
  Error.syntax_error (Loc.make $symbolstartpos $endpos)
    "`auto` applies only to lemmas and axioms. To have a predicate or function replaced by its \
     body where it is used, declare it `inline`"
}

callable_decl:
  id = callable_name; LPAREN; formals = formals_with_loc; RPAREN; returns = return_params; cs = contracts {
  let precond, postcond, contract_ext, opens = cs in
  let opens = single_opens_clause opens in
  let loc_params, formals = formals in
  Surface.Callable.decl ~kind:Func ~loc:(Loc.make $startpos(id) $endpos(id))
    ~formals ~returns ~precond ~postcond ~contract_ext ?opens ~loc_params id
}

callable_decl_out_vars:
  id = callable_name; LPAREN; formals = formals_with_loc; SEMICOLON; returns = var_decls_with_modifiers; RPAREN; cs = contracts {
  let precond, postcond, contract_ext, opens = cs in
  let opens = single_opens_clause opens in
  let loc_params, formals = formals in
  Surface.Callable.decl ~kind:Func ~loc:(Loc.make $startpos(id) $endpos(id))
    ~formals ~returns ~precond ~postcond ~contract_ext ?opens ~loc_params id
}


return_params:
| RETURNS; LPAREN; decls = var_decls_with_modifiers; RPAREN { decls }
| (* empty *) { [] }
   
var_decls_with_modifiers:
| decls = separated_list (COMMA, var_decl_with_modifiers) { decls }
;

(* One formal, which may be a *location*, `x.A.f`: that binds `x` as the Ref and
   names the field the callable operates on, so the declaration reads the way a
   call site does. The field comes from the enclosing functor; `x` is the only
   runtime argument. The two alternatives share their `var_modifier` prefix so
   the choice falls on COLON vs DOT and the grammar stays LR(1). *)
formal_with_loc:
| m = var_modifier; decl = bound_var {
  let implicit, ghost = m in
  `Var (Surface.Type.with_modifiers ~ghost ~implicit decl)
}
| m = var_modifier; x = plain_ident; DOT; f = qual_ident {
  let implicit, ghost = m in
  if implicit || ghost then
    Error.syntax_error (Loc.make $symbolstartpos $endpos)
      "A location parameter such as 'x.f' cannot be ghost or implicit";
  `Loc (Expr.to_qual_ident f,
        Type.mk_var_decl ~loc:(Loc.make $startpos(x) $endpos(x)) x Type.ref)
}
;

(* Formals, of which any number of *leading* ones may be locations -- more than
   one for a primitive that touches several locations in a single step, such as
   68k `CAS2` or z/Architecture `PLO` -- and any number of trailing ones implicit,
   so that a call can omit them. Kept as one list so the grammar stays
   unambiguous; the ordering rules are enforced here, where they can be reported
   properly. *)
formals_with_loc:
| fs = separated_list(COMMA, formal_with_loc) {
  let rec leading acc = function
    | (`Loc _ as f) :: tl -> leading (f :: acc) tl
    | tl -> (List.rev acc, tl)
  in
  let locs, rest = leading [] fs in
  if List.exists (function `Loc _ -> true | `Var _ -> false) rest then
    Error.syntax_error (Loc.make $symbolstartpos $endpos)
      "Location parameters such as 'x.f' must come before ordinary ones";
  let _ =
    List.fold_left (fun after_implicit -> function
      | `Var (d : Type.var_decl) ->
          if after_implicit && not d.var_implicit then
            Error.syntax_error d.var_loc
              (Printf.sprintf
                 "Implicit parameters must come last, but the explicit parameter %s \
                  follows one"
                 (Ident.name d.var_name));
          after_implicit || d.var_implicit
      | `Loc _ -> after_implicit) false rest
  in
  let flds =
    List.map (function `Loc (fld, _) -> fld | `Var _ -> assert false) locs
  in
  (flds, List.map (function `Loc (_, d) -> d | `Var d -> d) fs)
}
;

var_decl_with_modifiers:
| m = var_modifier; decl = bound_var {
  let implicit, ghost = m in
  Surface.Type.with_modifiers ~ghost ~implicit decl
}
;

contracts:
| c = contract; cs = contracts {
  let (pre1, post1, ext1, opens1) = c and (pre2, post2, ext2, opens2) = cs in
  (pre1 @ pre2, post1 @ post2, ext1 @ ext2, opens1 @ opens2)
}
| /* empty */ { [], [], [], [] }
;

contract:
| m = contract_mods; REQUIRES; e = expr {
  ([Surface.Stmt.spec ~atomic:m e], [], [], [])
}
| m = contract_mods; ENSURES; trigs = patterns; e = expr {
  ([], [Surface.Stmt.spec_with_triggers ~atomic:m ~triggers:trigs e], [], [])
}
| ce = contract_ext {
  ([], [], [ce], [])
}
| OPENS; LBRACE; RBRACE {
  ([], [], [], [ (Loc.make $symbolstartpos $endpos, []) ])
}
| OPENS; es = separated_nonempty_list(COMMA, opens_entry) {
  ([], [], [], [ (Loc.make $symbolstartpos $endpos, es) ])
}
;

(* An entry of an `opens` clause: an invariant, optionally applied to arguments of
   which a trailing run may be `_`. The `_`s are kept here and dropped by the type
   checker, once it has checked the entry against the invariant's arity. *)
opens_entry:
| x = qual_ident; es = loption(delimited(LPAREN, separated_list(COMMA, expr), RPAREN)) {
  let is_wildcard e =
    Expr.is_ident e && String.equal (Ident.name (Expr.to_ident e)) "_"
  in
  let rec check_trailing seen_wildcard = function
    | [] -> ()
    | e :: es ->
        if is_wildcard e then check_trailing true es
        else if seen_wildcard then
          Error.syntax_error (Expr.to_loc e)
            "In an opens clause, `_` may only stand for trailing arguments"
        else check_trailing false es
  in
  check_trailing false es;
  (Expr.to_qual_ident x, es)
}
;

%inline contract_mods:
| ATOMIC { true }
| (* empty *) { false }
;
  
(** Statements *)

stmt:
| ss = stmt_desc { List.map (Surface.Stmt.at ~loc:(Loc.make $symbolstartpos $endpos)) ss }

stmt_desc:
| s = stmt_wo_trailing_substmt { s }
| s = if_then_stmt { s }
| s = if_then_else_stmt { s }
| s = while_stmt { s }
| s = ghost_block { s }
| s = atomic_block { s }
;

stmt_no_short_if:
| ss = stmt_no_short_if_desc {
  Surface.Stmt.block_stmt ~loc:(Loc.make $symbolstartpos $endpos) @@
    List.map (Surface.Stmt.at ~loc:(Loc.make $symbolstartpos $endpos)) ss
}
    
    
stmt_no_short_if_desc:
| s = stmt_wo_trailing_substmt { s }
| s = if_then_else_stmt_no_short_if  { s }
| s = while_stmt_no_short_if  { s }
;

stmt_wo_trailing_substmt:
(* variable definition *)
| def = local_var_def; SEMICOLON {
    def
}
(* nested block *)
| s = block { [s] }
(* procedure call *)
| e = call_expr; SEMICOLON { [Surface.Stmt.call e] }
(* thread spawn *)
| SPAWN; id = qual_ident; LPAREN; args = separated_list(COMMA, expr); RPAREN; SEMICOLON {
  [Surface.Stmt.spawn (Expr.to_qual_ident id) args]
}
(* assignment / allocation / cas ... *)
| es = separated_nonempty_list(COMMA, expr); COLONEQ; rhs = assign_rhs; SEMICOLON {
  [Surface.Stmt.assign es rhs]
}
(* bind *)
| es = separated_nonempty_list(COMMA, expr); COLONPIPE; e = expr; SEMICOLON {
  [Surface.Stmt.bind es e]
}
(* havoc *)
| HAVOC; id = qual_ident; SEMICOLON { [Surface.Stmt.havoc (Expr.to_qual_ident id)] }

(* assume / assert / inhale / exhale *)
| goal = spec_goal; SEMICOLON {
  let sk, spec = goal in
  [Surface.Stmt.spec_stmt sk spec]
}
(* return *)
| RETURN; es = separated_list(COMMA, expr); SEMICOLON {
  [Surface.Stmt.return ~loc:(Loc.make $startpos(es) $endpos(es)) es]
}
(* unfold / fold / openInv / closeInv *)
| use_kind = USE; id = qual_ident; LPAREN; es = separated_list(COMMA, expr); RPAREN; SEMICOLON {
  [Surface.Stmt.use use_kind (Expr.to_qual_ident id) es]
}
| use_kind = USE; id = qual_ident; LPAREN; es = separated_list(COMMA, expr); RPAREN;
  LBRACKET wtns = separated_list(COMMA, existential_witness_or_bind) RBRACKET SEMICOLON {
  [Surface.Stmt.use use_kind (Expr.to_qual_ident id) ~witnesses:wtns es]
}
| f = stmt_ext { f }
;

  
existential_witness_or_bind:
| x = plain_ident COLONEQ e = expr {
  (x, e)
}

%public spec_goal:
| sk = SPEC; e = expr { (sk, Surface.Stmt.spec e) }
| sk = SPEC; name = plain_ident; COLON; e = expr {
  if sk <> Stmt.Assert then
    Error.syntax_error (Loc.make $startpos(name) $endpos(name))
      "A name is only allowed in assert statements";
  (sk, Surface.Stmt.spec ~name:name.Ident.ident_name e)
}

%public assign_rhs:
| NEW LPAREN fes = separated_list(COMMA, pair(qual_ident, option(preceded(COLON, expr)))) RPAREN {
  Surface.Stmt.new_rhs (List.map (fun (f, e_opt) -> (Expr.to_qual_ident f, e_opt)) fes)
}
| e = expr { Surface.Stmt.expr_rhs e }

local_var_def:
| g = ghost_modifier; v = VAR; decl = bound_var_opt_type; e = option(preceded(COLONEQ, assign_rhs)) {
  Surface.Stmt.local_var_def ~ghost:g ~const:v decl e ~rhs_loc:(Loc.make $startpos(e) $endpos(e))
}

    
var_def:
| g = ghost_modifier; v = VAR; decl = bound_var_opt_type; e = option(preceded(EQ, expr)) {
  Surface.Module.var_def ~ghost:g ~const:v decl e
}
| g = ghost_modifier; v = VAR; decl = bound_var_opt_type; COLONEQ; e = expr {
  Surface.Module.var_def ~ghost:g ~const:v decl (Some e)
}



    
%inline ghost_modifier:
| GHOST { true }
| (* empty *) { false }
;

%inline var_modifier:
| IMPLICIT; GHOST { true, true }
| g = ghost_modifier { false, g }
; 

  
%public block:
| LBRACE; stmts = list(stmt); RBRACE { Surface.Stmt.block (List.flatten stmts) }
;

ghost_block:
| LGHOSTBRACE; stmts = list(stmt); RGHOSTBRACE {
  [Surface.Stmt.ghost_block (List.flatten stmts)]
}
;

(* A *physically* atomic block: its body counts as one machine step however many
   statements it contains. Trusted -- Raven has no scheduler to enforce it. Not
   to be confused with the `atomic` modifier on a contract, which states the
   *logical* atomicity of a callable and is checked. *)
atomic_block:
| ATOMIC; LBRACE; stmts = list(stmt); RBRACE {
  [Surface.Stmt.atomic_block (List.flatten stmts)]
}
;

      
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
  [Surface.Stmt.cond e (Surface.Stmt.block_stmt ~loc:(Loc.make $startpos(st) $endpos(st)) st)
     (Surface.Stmt.skip ~loc:(Loc.make $endpos $endpos))]
}
;

if_then_else_stmt:
| IF; LPAREN; e = expr; RPAREN; st = stmt_no_short_if; ELSE; se = stmt { 
  [Surface.Stmt.cond e st (Surface.Stmt.block_stmt ~loc:(Loc.make $startpos(se) $endpos(se)) se)]
}
;

if_then_else_stmt_no_short_if:
| IF; LPAREN; e = expr; RPAREN; st = stmt_no_short_if; ELSE; se = stmt_no_short_if { 
  [Surface.Stmt.cond e st se]
}
;
  
while_stmt:
| WHILE; LPAREN; e = expr; RPAREN; cs = loop_contract_list; s = block {
  let invariants, contract_ext = cs in
  [Surface.Stmt.while_ ~loc:(Loc.make $startpos $endpos) ~invariants ~contract_ext e
     (Surface.Stmt.at ~loc:(Loc.make $startpos(s) $endpos(s)) s)]
}
| WHILE; LPAREN; e = expr; RPAREN; s = stmt {
  [Surface.Stmt.while_ ~loc:(Loc.make $startpos $endpos) e
     (Surface.Stmt.block_stmt ~loc:(Loc.make $startpos(s) $endpos(s)) s)]
}
;

while_stmt_no_short_if:
| WHILE; LPAREN; e = expr; RPAREN; s = stmt_no_short_if {
  [Surface.Stmt.while_ ~loc:(Loc.make $startpos $endpos) e s]
}
;

loop_contract_list:
| c = loop_contract; cs = loop_contract_list {
  let (inv, ext) = cs in
  match c with
  | `Invariant spec -> (spec :: inv, ext)
  | `Ext ce -> (inv, ce :: ext)
}
| c = loop_contract {
  match c with
  | `Invariant spec -> ([spec], [])
  | `Ext ce -> ([], [ce])
}
;

loop_contract:
| INVARIANT; e = expr { `Invariant (Surface.Stmt.spec e) }
| INVARIANT; name = plain_ident; COLON; e = expr {
  `Invariant (Surface.Stmt.spec ~name:name.Ident.ident_name e)
}
| ce = contract_ext { `Ext ce }
;

(** Expressions *)

primary:
| c = CONSTVAL { Surface.Expr.constant ~loc:(Loc.make $symbolstartpos $endpos) c }
| LPAREN; es = separated_list(COMMA, expr); RPAREN {
  Surface.Expr.tuple ~loc:(Loc.make $symbolstartpos $endpos) es
}
| LPAREN; e = expr; COLON; t = type_expr; RPAREN {
  Surface.Expr.annotated e t
}
| e = compr_expr { e }
| e = dot_expr { e }
| e = own_expr { e }
| e = au_expr { e }
;

enumeration_open:
| ENUM_OPEN { ($1, true) }
| LBRACEPIPE { ("{", true) }
| LBRACKETPIPE { ("[", true) }
| LENUMBRACE { ("{", false) }
| LBRACKET { ("[", false) }

enumeration_close:
| ENUM_CLOSE { ($1, true) }
| RBRACEPIPE { ("}", true) }
| RBRACKETPIPE { ("]", true) }
| RENUMBRACE { ("}", false) }
| RBRACKET { ("]", false) }

(* Retained as an extension point for nonstandard comprehensions. *)
%public compr_expr:
| opener = enumeration_open; es = separated_list(COMMA, expr);
  closer = enumeration_close; args = option(call) {
    let loc = Loc.make $symbolstartpos $endpos in
    ignore (checked_enumeration_name loc opener closer ~singleton:false);
    match args with
    | None -> Surface.Expr.enumeration ~loc (fst opener) es
    | Some args ->
        let singleton = match es with [e] when is_enumeration_hole e -> true | _ -> false in
        if not (List.is_empty es || singleton) then
          Error.syntax_error loc "Only empty and singleton constructor patterns can be called";
        let name = checked_enumeration_name loc opener closer ~singleton in
        Surface.Expr.call ~loc (QualIdent.from_ident name) args
  }
| opener = enumeration_open; entries = map_entries; closer = enumeration_close {
    let loc = Loc.make $symbolstartpos $endpos in
    (match opener, closer with
     | ("{", false), ("}", false) -> ()
     | _ -> Error.syntax_error loc "A map literal is delimited by braces");
    let entries, default = entries in
    Surface.Expr.map_literal ~loc entries default
  }
| opener = enumeration_open; v = bound_var; COLONCOLON; e = expr;
  closer = enumeration_close {
    let loc = Loc.make $symbolstartpos $endpos in
    check_set_comprehension loc opener closer;
    Surface.Expr.set_compr ~loc v e
  }
;
  
(* The entries of a map literal, and the value at every other key. *)
map_entries:
| ELSE; default = expr { ([], default) }
| k = expr; COLONEQ; v = expr; COMMA; entries = map_entries {
    let entries, default = entries in
    ((k, v) :: entries, default)
  }
| expr; COLONEQ; expr {
    Error.syntax_error (Loc.make $endpos $endpos)
      "A map literal needs a value for the other keys: add `else e`"
  }

dot_expr:
(*| MAP LT var_type, var_type GT LPAREN expr_list_opt RPAREN {*)
| p = qual_ident_expr; co = call_opt { co p }
;

own_expr:
| OWN; LPAREN; es = expr_list; RPAREN {
  Surface.Expr.own ~loc:(Loc.make $symbolstartpos $endpos) es
}

au_expr:
| AU; LT; qid = qual_ident; GT; LPAREN; es = expr_list; RPAREN {
  Surface.Expr.au ~loc:(Loc.make $symbolstartpos $endpos) (Expr.to_qual_ident qid) es
}
| AUCOMMIT LT qid=qual_ident GT LPAREN es=expr_list; RPAREN {
  Surface.Expr.au_commit ~loc:(Loc.make $symbolstartpos $endpos) (Expr.to_qual_ident qid) es
}

call_expr:
| p = qual_ident_expr; es = call {
  Surface.Expr.call ~loc:(Loc.make $symbolstartpos $endpos) (Expr.to_qual_ident p) es
}
  
call:
| LPAREN; es = separated_list(COMMA, call_arg); RPAREN { es }

(* A call argument, optionally annotated with a type (`f(e: T)`) without needing
   the extra parens the standalone `(e: T)` form (see `primary`) would require. *)
call_arg:
| e = expr { e }
| e = expr; COLON; t = type_expr { Surface.Expr.annotated e t }
  
call_opt:
| es = call { 
  fun p ->
    Surface.Expr.call ~loc:(Loc.merge (Expr.to_loc p) (Loc.make $symbolstartpos $endpos))
      (Expr.to_qual_ident p) es
}
| (* empty *) { fun e -> e }
  
qual_ident_expr:
| x = qual_ident { x }
| p = lookup_or_update_expr DOT x = qual_ident {
  Surface.Expr.field ~loc:(Loc.make $symbolstartpos $endpos) ~field_loc:(Expr.to_loc x) p
    (Expr.to_qual_ident x)
}
| p = lookup_or_update_expr DOT LPAREN x = qual_ident RPAREN {
  Surface.Expr.field ~loc:(Loc.make $symbolstartpos $endpos) ~field_loc:(Expr.to_loc x) p
    (Expr.to_qual_ident x)
}

%public qual_ident:
| x = ident { x }
| m = mod_ident; DOT; x = enumeration_name {
  Surface.Expr.var ~loc:(Loc.make $symbolstartpos $endpos) (QualIdent.append m x)
}
| m = mod_ident; DOT; x = expression_name {
  Surface.Expr.var ~loc:(Loc.make $symbolstartpos $endpos) (QualIdent.append m x)
}

mod_ident:
| x = MODIDENT { QualIdent.from_ident x}
| x = mod_ident; DOT; y = MODIDENT { QualIdent.append x y}

(* Ordinary names and user-defined symbolic operators. *)
%public plain_ident:
| x = IDENT { x }
| UNDERSCORE { Ident.make (Loc.make $symbolstartpos $endpos) "_" 0 }

%public decl_name:
| x = plain_ident { x }
| x = MULTOPSYM { x }
| x = ADDOPSYM { x }
| x = right_assoc_binary_op_ident { x }
| x = RELOPSYM { x }
| x = EQOPSYM { x }
| x = ANDOPSYM { x }
| x = OROPSYM { x }
;

fixed_operator_name:
| LT { Ident.make (Loc.make $symbolstartpos $endpos) "<" 0 }
| LEQ { Ident.make (Loc.make $symbolstartpos $endpos) "<=" 0 }
| UNION { Ident.make (Loc.make $symbolstartpos $endpos) "++" 0 }
| INTER { Ident.make (Loc.make $symbolstartpos $endpos) "**" 0 }
| DIFF { Ident.make (Loc.make $symbolstartpos $endpos) "--" 0 }
| SUBSETEQ { Ident.make (Loc.make $symbolstartpos $endpos) "subseteq" 0 }
| CHOOSE { Ident.make (Loc.make $symbolstartpos $endpos) "choose" 0 }
| IN { Ident.make (Loc.make $symbolstartpos $endpos) "in" 0 }

mixfix_name:
| UNDERSCORE; LBRACKET; UNDERSCORE; RBRACKET {
  Ident.make (Loc.make $symbolstartpos $endpos) "_[_]" 0
}
| UNDERSCORE; LBRACKET; UNDERSCORE; COLONEQ; UNDERSCORE; RBRACKET {
  Ident.make (Loc.make $symbolstartpos $endpos) "_[_:=_]" 0
}
| UNDERSCORE; LBRACKET; UNDERSCORE; DOTDOT; UNDERSCORE; RBRACKET {
  Ident.make (Loc.make $symbolstartpos $endpos) "_[_.._]" 0
}
| UNDERSCORE; LBRACKET; DOTDOT; UNDERSCORE; RBRACKET {
  Ident.make (Loc.make $symbolstartpos $endpos) "_[.._]" 0
}
| UNDERSCORE; LBRACKET; UNDERSCORE; DOTDOT; RBRACKET {
  Ident.make (Loc.make $symbolstartpos $endpos) "_[_..]" 0
}

enumeration_name:
| opener = enumeration_open; closer = enumeration_close {
  checked_enumeration_name (Loc.make $symbolstartpos $endpos) opener closer ~singleton:false
}
| opener = enumeration_open; UNDERSCORE; closer = enumeration_close {
  checked_enumeration_name (Loc.make $symbolstartpos $endpos) opener closer ~singleton:true
}

callable_name:
| x = decl_name { x }
| x = fixed_operator_name { x }
| x = mixfix_name { x }
| x = enumeration_name { x }

%public ident:
| x = expression_name { Surface.Expr.ident ~loc:(Loc.make $symbolstartpos $endpos) x }
;

expression_name:
| x = decl_name { x }
| x = fixed_operator_name { x }

lookup_or_update_expr:
| e = primary; cont = lookup_or_update_opt { cont e }

(*
lookup_expr:
| e1 = qual_ident_expr; e_fn = lookup; { e_fn e1 }
| LPAREN; e1 = expr; RPAREN; e_fn = lookup; { e_fn e1 }*)

(* %public so that extensions can add indexed forms of their own. *)
%public lookup_or_update_opt:
| LBRACKET; DOTDOT; hi = expr; RBRACKET; args = option(call); cont = lookup_or_update_opt {
  fun e -> cont (mixfix_application (Loc.make $symbolstartpos $endpos) "_[.._]" e [hi] args)
}
| LBRACKET; lo = expr; DOTDOT; RBRACKET; args = option(call); cont = lookup_or_update_opt {
  fun e -> cont (mixfix_application (Loc.make $symbolstartpos $endpos) "_[_..]" e [lo] args)
}
| LBRACKET; lo = expr; DOTDOT; hi = expr; RBRACKET; args = option(call); cont = lookup_or_update_opt {
  fun e -> cont (mixfix_application (Loc.make $symbolstartpos $endpos) "_[_.._]" e [lo; hi] args)
}
| (* empty *) { fun p -> p }
| LBRACKET; e2 = expr; COLONEQ; e3 = expr; RBRACKET; args = option(call); cont = lookup_or_update_opt {
  fun e ->
    let e_upd =
      mixfix_application (Loc.make $symbolstartpos $endpos) "_[_:=_]" e [e2; e3] args
    in
    cont e_upd
}
| LBRACKET; e2 = expr; RBRACKET; args = option(call); cont = lookup_or_update_opt {
  fun e1 ->
    let e1_lookup = mixfix_application (Loc.make $symbolstartpos $endpos) "_[_]" e1 [e2] args in
    cont e1_lookup
}
| n = HASH; cont = lookup_or_update_opt {
  let loc = Loc.make $startpos(n) $endpos(n) in
  fun e1 -> cont (Surface.Expr.tuple_get ~loc ~index_loc:loc e1 (Int64.to_int n))
}

  
%public unary_expr:
| e = lookup_or_update_expr { e }
(*| e = ident { e }*)
| MINUS; e = unary_expr { Surface.Expr.neg ~loc:(Loc.make $symbolstartpos $endpos) e }
| e = unary_expr_not_plus_minus { e }
;

unary_expr_not_plus_minus:
| NOT; e = unary_expr  { Surface.Expr.not_ ~loc:(Loc.make $symbolstartpos $endpos) e }
;

(* An operator, with its location. *)
mult_op:
| op = MULTOP { (binop_of_constr op, Loc.make $symbolstartpos $endpos) }
| INTER { (Surface.Expr.Inter, Loc.make $symbolstartpos $endpos) }
| op = MULTOPSYM { (Surface.Expr.User op, Loc.make $symbolstartpos $endpos) }

mult_expr:
| e = unary_expr { e }
| e1 = mult_expr; op = mult_op; e2 = unary_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) ~op_loc:(snd op) (fst op) e1 e2
  }
;

add_op:
| op = ADDOP { (binop_of_constr op, Loc.make $symbolstartpos $endpos) }
| UNION { (Surface.Expr.Union, Loc.make $symbolstartpos $endpos) }
| DIFF { (Surface.Expr.Diff, Loc.make $symbolstartpos $endpos) }
| MINUS { (Surface.Expr.Minus, Loc.make $symbolstartpos $endpos) }
| op = ADDOPSYM { (Surface.Expr.User op, Loc.make $symbolstartpos $endpos) }

add_expr:
| e = mult_expr { e }
| e1 = add_expr; op = add_op; e2 = mult_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) ~op_loc:(snd op) (fst op) e1 e2
  }
;

(* The bare identifier of a right-associative infix operator, as opposed to
   [right_assoc_binary_op] below which wraps it into an [Expr.constr] ready to
   apply. Exposed separately (and %public) so a match arm can name the same
   constructor infix, `case hd :: tl => ...` -- see matchExt_parser.mly's
   `match_arm_expr` -- without unwrapping a `Var` back out of a `constr`. `::`
   is declared here directly, an ordinary alternative alongside RABINOPSYM. *)
%public right_assoc_binary_op_ident:
| op = RABINOPSYM { op }
| COLONCOLON { Ident.make (Loc.make $symbolstartpos $endpos) "::" 0 }

%public right_assoc_binary_op:
| op = right_assoc_binary_op_ident { Surface.Expr.User op }

right_assoc_binary_op_expr:
| e = add_expr { e }
| e1 = add_expr; op = right_assoc_binary_op; e2 = right_assoc_binary_op_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) op e1 e2
}
    
%public rel_expr:
| c = comp_seq {
  match c with
  | e, [] -> e
  | _, comps -> Base.List.reduce_exn comps ~f:(fun e1 e2 -> Surface.Expr.conj ~loc:(Loc.merge (Expr.to_loc e1) (Expr.to_loc e2)) [e1; e2])
}
| e1 = rel_expr; IN; e2 = right_assoc_binary_op_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) In e1 e2
  } 
| e1 = rel_expr; NOTIN; e2 = right_assoc_binary_op_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) Not_in e1 e2
  }
;

comp_op:
| LT { (Surface.Expr.Lt, Loc.make $symbolstartpos $endpos) }
| GT { (Surface.Expr.Gt, Loc.make $symbolstartpos $endpos) }
| LEQ { (Surface.Expr.Leq, Loc.make $symbolstartpos $endpos) }
| GEQ { (Surface.Expr.Geq, Loc.make $symbolstartpos $endpos) }
| SUBSETEQ { (Surface.Expr.Subseteq, Loc.make $symbolstartpos $endpos) }
| op = RELOPSYM { (Surface.Expr.User op, Loc.make $symbolstartpos $endpos) }
;

comp_seq:
| e = right_assoc_binary_op_expr { (e, []) }
| e1 = right_assoc_binary_op_expr; op = comp_op; cseq = comp_seq {
  let e2, comps = cseq in
  let loc1 = Expr.to_loc e1 in
  let loc2 = Expr.to_loc e2 in
  (e1, Surface.Expr.binary ~loc:(Loc.merge loc1 loc2) ~op_loc:(snd op) (fst op) e1 e2 :: comps)
}
;
  
(* This level and `rel_expr` above are %public so an extension's own parser fragment can
   add a production at exactly this precedence level -- see matchExt_parser.mly's `is`,
   which is a comparison and has to bind like one (tighter than `&&`/`==>`). Menhir's
   --merge_into only lets a fragment reference a nonterminal that is declared %public
   here; the levels of this ladder are otherwise invisible to fragment files. *)
%public eq_expr:
| e = rel_expr { e }
| e1 = eq_expr; EQEQ; e2 = eq_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) Eq e1 e2
  }
| e1 = eq_expr; NEQ; e2 = eq_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) Neq e1 e2
  }
| e1 = eq_expr; op = EQOPSYM; e2 = eq_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) (User op) e1 e2
  }
;

and_expr:
| e = eq_expr { e }
| e1 = and_expr; AND; e2 = eq_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) And e1 e2
  }
| e1 = and_expr; op = ANDOPSYM; e2 = eq_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) (User op) e1 e2
  }
;

or_expr:
| e = and_expr { e }
| e1 = or_expr; OR; e2 = and_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) Or e1 e2
  }
| e1 = or_expr; op = OROPSYM; e2 = and_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) (User op) e1 e2
  }
;



impl_expr:
| e = or_expr { e }
| e1 = or_expr; IMPLIES; e2 = impl_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) Impl e1 e2
  }
;

iff_expr:
| e = impl_expr { e }
| e1 = iff_expr IFF e2 = iff_expr {
    Surface.Expr.binary ~loc:(Loc.make $symbolstartpos $endpos) Iff e1 e2
  }
;

(* Right-associative: `a ? b : c ? d : e` is `a ? b : (c ? d : e)`. *)
ite_expr:
| e = iff_expr { e }
| e1 = iff_expr; QMARK; e2 = ite_expr; COLON; e3 = ite_expr {
    Surface.Expr.ite ~loc:(Loc.make $symbolstartpos $endpos) e1 e2 e3
  }
;
    
quant_var:
| v = bound_var { v }
;

bound_var:
| x = plain_ident; COLON; t = type_expr {
    Surface.Type.var_decl ~loc:(Loc.make $symbolstartpos $endpos) x t
  }
;

bound_var_opt_type:
| x = plain_ident { Surface.Type.local_decl ~loc:(Loc.make $symbolstartpos $endpos) x None }
| x = plain_ident; COLON; t = type_expr {
  Surface.Type.local_decl ~loc:(Loc.make $symbolstartpos $endpos) x (Some t)
} 
;

%public type_expr:
| ct = CONSTTYPE { Surface.Type.constant ~loc:(Loc.make $symbolstartpos $endpos) ct }
| ATOMICTOKEN LT qid = qual_ident GT {
  Surface.Type.atomic_token ~loc:(Loc.make $symbolstartpos $endpos) (Expr.to_qual_ident qid) }
| ct = TYPECONSTR LBRACKET ts = separated_list(COMMA, type_expr) RBRACKET {
  Surface.Type.constr ~loc:(Loc.make $symbolstartpos $endpos) ct ts
  }
| x = mod_ident { Surface.Type.named ~loc:(Loc.make $symbolstartpos $endpos) x [] }
| LPAREN ts = separated_list(COMMA, type_expr) RPAREN {
  Surface.Type.tuple ~loc:(Loc.make $symbolstartpos $endpos) ts }
| x = mod_ident LBRACKET; ts = type_expr_list; RBRACKET {
  Surface.Type.named ~loc:(Loc.make $symbolstartpos $endpos) x ts }
    
  
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
    Surface.Expr.quant ~loc:(Loc.make $symbolstartpos $endpos) ~triggers:trigs q vs e
  }
;

patterns:
| LBRACE; es = expr_list; RBRACE; trgs = patterns { es :: trgs }
| /* empty */ { [] }

%public expr:
| e = quant_expr { e } 
;

%public expr_list:
| e = expr; COMMA; es = expr_list { e :: es }
| e = expr { [e] }
;
