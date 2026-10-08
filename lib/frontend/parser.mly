%{

open Util
open Ast
(*open Base*)

(* A callable has at most one `opens` clause. *)
let single_opens_clause = function
  | [] -> None
  | [ (_, mask) ] -> Some mask
  | _ :: (loc, _) :: _ ->
      Error.syntax_error loc "A callable may have at most one opens clause"

(* Checks that `inline`, if given, is applied to a function or predicate. *)
let inline_modifier ~loc (kind : Callable.call_kind) (is_inline : bool) : bool =
  match kind with
  | Invariant when is_inline -> Error.syntax_error loc "An invariant cannot be inline"
  | _ -> is_inline

(* The indexed assignment `x[i] := v` is `x := x[i := v]`, and `x[i][j] := v` is
   `x := x[i := x[i][j := v]]`. The type checker gives it its meaning: an update of a
   map, or whatever an extension claims it to be. *)
let rec index_assign base index value =
  let loc = Loc.merge (Expr.to_loc base) (Expr.to_loc value) in
  let update = Expr.mk_app ~typ:Type.any ~loc MapUpdate [ base; index; value ] in
  match base with
  | Expr.App (Var qual_ident, [], _) when QualIdent.is_local qual_ident ->
      Stmt.Assign { assign_lhs = [ qual_ident ]; assign_rhs = update; assign_is_init = false }
  | Expr.App (MapLookUp, [ base'; index' ], _) -> index_assign base' index' update
  | _ ->
      Error.syntax_error (Expr.to_loc base)
        "Expected a variable, possibly indexed, on the left-hand side of an indexed assignment"

(* A sealed module without parameters, `module M :> I { ... }`, as the module `M$Impl : I`
   with its body and the sealed instance `module M :> I = M$Impl`. *)
let expand_sealed_module (member : Module.module_instr) : Module.module_instr list =
  let open Module in
  match member with
  | SymbolDef (ModDef ({ mod_decl = decl; _ } as mod_def))
    when decl.mod_decl_is_sealed && List.is_empty decl.mod_decl_formals
         && not decl.mod_decl_is_interface -> (
      match decl.mod_decl_returns with
      | [ (iface, _) ] ->
          let loc = decl.mod_decl_loc in
          let impl_name =
            Ident.make loc (decl.mod_decl_name.ident_name ^ ProgUtils.sealed_impl_suffix) 0
          in
          let impl =
            ModDef { mod_def with
                     mod_decl = { decl with mod_decl_name = impl_name; mod_decl_is_sealed = false } }
          in
          let view =
            ModInst { mod_inst_name = decl.mod_decl_name;
                      mod_inst_type = iface;
                      mod_inst_def = Some (QualIdent.from_ident impl_name, []);
                      mod_inst_is_interface = false;
                      mod_inst_is_free = false;
                      mod_inst_is_sealed = true;
                      mod_inst_loc = loc }
          in
          [ SymbolDef impl; SymbolDef view ]
      | _ -> [ member ])
  | _ -> [ member ]

(* A local variable definition, followed by the assignment of its initial value, if any. *)
let mk_local_var_def ~ghost ~const decl rhs_opt ~rhs_loc =
  let decl =
    Type.{ decl with
           var_type = decl.var_type |> Type.set_ghost ghost;
           var_ghost = ghost;
           var_const = const;
         }
  in
  match rhs_opt with
  | Some rhs ->
      let stmt, default_expr_optn = rhs ([Expr.from_var_decl decl], true) in
      let var_init =
        match stmt, default_expr_optn with
        | Stmt.Basic (Assign assign_desc), None -> Some assign_desc.assign_rhs
        | _, Some expr -> Some (Expr.set_loc expr rhs_loc)
        | _ -> None
      in
      [Stmt.(Basic (VarDef { var_decl = decl; var_init; var_is_free = NotFree })); stmt]
  | None ->
      [Stmt.(Basic (VarDef { var_decl = decl; var_init = None; var_is_free = NotFree }))]

%}

%token <Ast.Ident.t> IDENT MODIDENT
%token <Ast.Expr.constr> CONSTVAL
%token <Ast.Type.constr> CONSTTYPE
%token <Ast.Type.constr * int> TYPECONSTR
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token LBRACEPIPE RBRACEPIPE LBRACKETPIPE RBRACKETPIPE LGHOSTBRACE RGHOSTBRACE
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
%token CASE DATA ATOMICTOKEN FIELD
%token ATOMIC GHOST IMPLICIT REP AUTO INLINE WITH
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
| INCLUDE s = STRINGVAL; files = includes { (s, Loc.make $startpos(s) $endpos(s)) :: files }
| /* empty */ { [] }

(** Member Definitions *)

module_def:
| is_interface = MODULE; decl = module_header; def = module_inst_or_impl_or_decl {
  let open Module in
  match def with
  | ModDef impl ->
      ModDef { impl with mod_decl = { decl with mod_decl_is_interface = is_interface } }
  | ModInst ma ->
      if decl.mod_decl_formals <> [] then
        Error.syntax_error (Loc.make $startpos(def) $startpos(def))
          "A module with parameters cannot be defined with '=' (module instantiation syntax); give it a body in '{ ... }' instead"
      else if decl.mod_decl_is_sealed && Option.is_none ma.mod_inst_def then
        Error.syntax_error (Loc.make $startpos(decl) $endpos(decl))
          (Printf.sprintf !"Module %{Ident} has no definition, so it cannot be sealed with ':>'"
             decl.mod_decl_name)
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
        | [ (mod_inst_type, []) ], _
        | [], Some (mod_inst_type, _) -> mod_inst_type
        | [], None ->
            Error.syntax_error (Loc.make $endpos(decl) $endpos(decl))
              (Printf.sprintf !"Module %{Ident} has no body and no interface: write 'module %{Ident} : I' naming the interface it stands for"
                 decl.mod_decl_name decl.mod_decl_name)
        in
        ModInst { ma with
                  mod_inst_type;
                  mod_inst_name = decl.mod_decl_name;
                  mod_inst_is_interface = is_interface;
                  mod_inst_is_free = false;
                  mod_inst_is_sealed = decl.mod_decl_is_sealed;
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
      mod_decl_returns = fst rt;
      mod_decl_is_sealed = snd rt;
      mod_decl_loc = Loc.make $startpos(id) $endpos(id);
    }
  in
  decl
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
| EQ; mod_name = mod_ident; args = mod_inst_args {
  Module.( ModInst { mod_inst_name = Ident.make Loc.dummy "" 0; (* dummy *)
                     mod_inst_type = QualIdent.make [] (Ident.make Loc.dummy "" 0); (* dummy *)
                     mod_inst_def = Some (mod_name, args);
                     mod_inst_is_interface = false;
                     mod_inst_is_sealed = false; mod_inst_is_free = false;
                     mod_inst_loc = Loc.dummy;
                   } )
}
| (* empty *) {
  Module.( ModInst { mod_inst_name = Ident.make Loc.dummy "" 0; (* dummy *)
                     mod_inst_type = QualIdent.make [] (Ident.make Loc.dummy "" 0); (* dummy *)
                     mod_inst_def = None;
                     mod_inst_is_interface = false;
                     mod_inst_is_sealed = false; mod_inst_is_free = false;
                     mod_inst_loc = Loc.dummy;
                   } )
}

mod_inst_args:
| LBRACKET tps = separated_list(COMMA, type_expr) RBRACKET {
  List.map (function
    | Type.App (Type.Var qi, [], _) -> Module.ModArg qi
    | tp -> Module.TypeArg tp) tps
}
| { [] }
    
member_def_list_opt:
| m = member_def_maybe_free; ms = member_def_list_opt { expand_sealed_module m @ ms }
| (* empty *) { [] }

member_def_maybe_free:
| is_free = free symbol = member_def {
  Module.SymbolDef (if is_free then Symbol.set_free symbol else symbol) }
| imp = import_dir { Module.Import imp }

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
| g = ghost_modifier; FIELD x = IDENT; COLON; t = type_expr {
    let decl =
      Module.{ field_name = x;
               field_type = Type.mk_fld (Loc.make $startpos(t) $endpos(t)) t |> Type.set_ghost g;
               field_is_ghost = g;
               field_alias = None;
               field_loc = Loc.make $symbolstartpos $endpos
           }
    in
    decl
  }
(* Manifest field: `field f = M.g` denotes an existing field rather than
   declaring a new one, the counterpart of `rep type T = Int` for types. The
   type and ghost-ness are taken from the target and checked in Typing. *)
| g = ghost_modifier; FIELD x = IDENT; EQ; target = qual_ident {
    let decl =
      Module.{ field_name = x;
               field_type = Type.mk_fld (Loc.make $startpos(target) $endpos(target)) Type.any |> Type.set_ghost g;
               field_is_ghost = g;
               field_alias = Some (Expr.to_qual_ident target);
               field_loc = Loc.make $symbolstartpos $endpos
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
  Type.mk_data (QualIdent.from_ident (Ident.make Loc.dummy "" 0)) decls (Loc.make $symbolstartpos $endpos)
}

variant_decl:
| CASE; id = decl_name args = option(variant_args) {
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
  let def =
    let ghostify_decls =
      Base.List.map ~f:(fun decl -> Type.{ decl with var_ghost = true; var_type = set_ghost true decl.var_type })
    in
    let call_decl_returns =
      match call_decl_kind with
      | Lemma | Pred | Invariant ->
          ghostify_decls def.call_decl.call_decl_returns
      | _ ->
          def.call_decl.call_decl_returns
    in
    { def with call_decl = { def.call_decl with call_decl_kind; call_decl_is_auto; call_decl_returns } } in
  let proc_body = Option.map body ~f:(fun s ->
    Stmt.{ stmt_desc = s; stmt_loc = Loc.make $startpos(body) $endpos(body) })
  in
  { def with call_def = ProcDef { proc_body } }
}

proc_kind:
| PROC { (Callable.Proc, false, false) }
| is_auto = ioption(AUTO); LEMMA { (Callable.Lemma, false, is_auto <> None) }
| is_auto = ioption(AUTO); AXIOM { (Callable.Lemma, true, is_auto <> None) }
    
func_def:
| def = func_decl; body = option(delimited(LBRACE, expr, RBRACE)) {
  let open Callable in
  let implicify_decls =
    Base.List.map ~f:(fun decl ->
      Type.{ decl with var_ghost = true; var_implicit = true; var_type = set_ghost true decl.var_type })
  in
  let call_decl_returns =
    match def.call_decl.call_decl_kind with
    | Pred | Invariant ->
        implicify_decls def.call_decl.call_decl_returns
    | _ ->
        def.call_decl.call_decl_returns
  in
  { call_decl = { def.call_decl with call_decl_returns };
    call_def = FuncDef { func_body = body }
  }
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
             mod_inst_is_sealed = false; mod_inst_is_free = false;
             mod_inst_loc = Loc.make $symbolstartpos $endpos;
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
  { import_name; import_all; import_loc = Loc.make $symbolstartpos $endpos }
}
| IMPORT; id = mod_ident { { import_name = id; import_all = false; import_loc = Loc.make $symbolstartpos $endpos } }
    
type_decl:
| m = type_mod; TYPE; id = MODIDENT {
  let ta =
    Module.{ type_def_name = id;
             type_def_expr = None;
             type_def_rep = m;
             type_def_is_free = false;
             type_def_loc = Loc.make $symbolstartpos $endpos }
  in
  ta
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
  Callable.mk_call_decl ~kind:Func ~name:id ~loc:(Loc.make $startpos(id) $endpos(id))
    ~formals ~returns ~precond ~postcond ~contract_ext ?opens ~loc_params ()
}

callable_decl_out_vars:
  id = callable_name; LPAREN; formals = formals_with_loc; SEMICOLON; returns = var_decls_with_modifiers; RPAREN; cs = contracts {
  let precond, postcond, contract_ext, opens = cs in
  let opens = single_opens_clause opens in
  let loc_params, formals = formals in
  Callable.mk_call_decl ~kind:Func ~name:id ~loc:(Loc.make $startpos(id) $endpos(id))
    ~formals ~returns ~precond ~postcond ~contract_ext ?opens ~loc_params ()
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
  `Var Type.{ decl with
              var_type = decl.var_type |> Type.set_ghost ghost;
              var_ghost = ghost;
              var_implicit = implicit;
            }
}
| m = var_modifier; x = IDENT; DOT; f = qual_ident {
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
  let decl =
    Type.{ decl with
           var_type = decl.var_type |> Type.set_ghost ghost;
           var_ghost = ghost;
           var_implicit = implicit;
         }
  in
  decl
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
  let spec =
    Stmt.{ spec_form = e;
           spec_atomic = m;
           spec_comment = None;
           spec_error = [];
           spec_source = None; spec_trigs = [];
         }
  in
  ([spec], [], [], [])
}
| m = contract_mods; ENSURES; trigs = patterns; e = expr {
  let spec =
    Stmt.{ spec_form = e;
           spec_atomic = m;
           spec_comment = None;
           spec_error = [];
           spec_source = None;
           spec_trigs = trigs;
         }
  in
  ([], [spec], [], [])
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
| ss = stmt_desc { List.map (fun s -> Stmt.{ stmt_desc = s; stmt_loc = Loc.make $symbolstartpos $endpos }) ss }

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
  Stmt.mk_block_stmt ~loc:(Loc.make $symbolstartpos $endpos) @@
    List.map (fun s -> Stmt.{ stmt_desc = s; stmt_loc = Loc.make $symbolstartpos $endpos }) ss
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
| e = call_expr; SEMICOLON {
  let assign =
    Stmt.{ assign_lhs = [];
           assign_rhs = e;
           assign_is_init = false;
         }
  in
  [Stmt.(Basic (Assign assign))]
}
(* thread spawn *)
| SPAWN; id = qual_ident; LPAREN; args = separated_list(COMMA, expr); RPAREN; SEMICOLON {
  let open Stmt in
  let call =
    { call_lhs = [];
      call_name = Expr.to_qual_ident id;
      call_args = args;
      call_is_spawn = true;
      call_is_init = false;
    }
  in
  [Basic (Call call)]
}
(* assignment / allocation / cas ... *)
| es = separated_nonempty_list(COMMA, expr); COLONEQ; rhs = assign_rhs; SEMICOLON {
  [let stmt, _def_arg = rhs (es, false) in stmt] 
}
(* bind *)
| es = separated_nonempty_list(COMMA, expr); COLONPIPE; e = expr; SEMICOLON {
  let vs = List.map (function
    | Expr.(App (Var qual_ident, [], _))
      when QualIdent.is_local qual_ident -> qual_ident
    | e -> Error.syntax_error (Expr.to_loc e) "Expected single field location or local variables on left-hand side of assignment")
      es 
  in
  let bind =
    Stmt.{ bind_lhs = vs;
           bind_rhs = mk_spec e;
         }
  in
  [Stmt.(Basic (Bind bind))]
}
(* havoc *)
| HAVOC; id = qual_ident; SEMICOLON { 
  [Stmt.(Basic (Havoc { havoc_var = (Expr.to_qual_ident id); havoc_is_init = false; } ))]
}

(* assume / assert / inhale / exhale *)
| sk = SPEC; e = expr; mk_spec_stmt = with_clause {
  mk_spec_stmt sk e
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
  [Stmt.(Basic (Return e))]
}
(* unfold / fold / openInv / closeInv *)
| use_kind = USE; id = qual_ident; LPAREN; es = separated_list(COMMA, expr); RPAREN; SEMICOLON {
  [Stmt.(Basic (Use {
    use_kind = use_kind; 
    use_name = Expr.to_qual_ident id; 
    use_args = es;
    use_witnesses_or_binds = []
  }))]
}
| use_kind = USE; id = qual_ident; LPAREN; es = separated_list(COMMA, expr); RPAREN;
  LBRACKET wtns = separated_list(COMMA, existential_witness_or_bind) RBRACKET SEMICOLON {
  [Stmt.(Basic (Use {
    use_kind = use_kind; 
    use_name = Expr.to_qual_ident id; 
    use_args = es;
    use_witnesses_or_binds = wtns
  }))]
}
| f = stmt_ext { f }
;

  
existential_witness_or_bind:
| x = IDENT COLONEQ e = expr {
  (x, e)
}

with_clause:
| SEMICOLON {
  fun sk e ->
    let open Stmt in
    let spec = { spec_form = e;
                 spec_atomic = false;
                 spec_comment = None;
                 spec_error = [];
                 spec_source = None; spec_trigs = []; }
    in
    [Basic (Spec (sk, spec))]
}
  
%public assign_rhs:
| NEW LPAREN fes = separated_list(COMMA, pair(qual_ident, option(preceded(COLON, expr)))) RPAREN {
  function
    | [Expr.App(Expr.Var x, _, _)], assign_is_init ->
        let new_descr = Stmt.{
          new_lhs = x;
          new_args = List.map (fun (f, e_opt) -> (Expr.to_qual_ident f, e_opt)) fes;
          new_is_init = assign_is_init;
        }
        in
        Stmt.(Basic (New new_descr)), Some (Expr.mk_null ())
    | es, _ -> Error.syntax_error (es |> List.hd |> Expr.to_loc) ("Result of allocation must be assigned to a single variable")
}
| e = expr {
  function 
    | [Expr.(App (Read, [field_write_ref; App (Var field_write_field, [], _)], _))], _ ->
        Basic (FieldWrite { field_write_ref; field_write_field; field_write_val = e }), None
    | [Expr.(App (MapLookUp, [base; index], _))], _ ->
        Basic (index_assign base index e), None
    | es, assign_is_init ->
        let vs = List.map (function
          | Expr.(App (Var qual_ident, [], _))
            when QualIdent.is_local qual_ident -> qual_ident
          | e -> Error.syntax_error (Expr.to_loc e) "Expected a single field location, a single indexed location, or local variables on left-hand side of assignment")
            es 
        in
        Basic (Assign { assign_lhs = vs; assign_rhs = e; assign_is_init }), None
}

local_var_def:
| g = ghost_modifier; v = VAR; decl = bound_var_opt_type; e = option(preceded(COLONEQ, assign_rhs)) {
  mk_local_var_def ~ghost:g ~const:v decl e ~rhs_loc:(Loc.make $startpos(e) $endpos(e))
}

    
var_def:
| g = ghost_modifier; v = VAR; decl = bound_var_opt_type; e = option(preceded(EQ, expr)) {
  let decl =
    Type.{ decl with
           var_type = decl.var_type |> Type.set_ghost g;
           var_ghost = g;
           var_const = v;
         }
  in
  Stmt.{ var_decl = decl; var_init = e; var_is_free = NotFree }
}
| g = ghost_modifier; v = VAR; decl = bound_var_opt_type; COLONEQ; e = expr {
  let decl =
    Type.{ decl with
           var_type = decl.var_type |> Type.set_ghost g;
           var_ghost = g;
           var_const = v;
         }
  in
  Stmt.{ var_decl = decl; var_init = Some e; var_is_free = NotFree }
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
| LBRACE; stmts = list(stmt); RBRACE { Stmt.mk_block (List.flatten stmts) }
;

ghost_block:
| LGHOSTBRACE; stmts = list(stmt); RGHOSTBRACE {
  [Stmt.mk_block ~kind:Stmt.Ghost (List.flatten stmts)]
}
;

(* A *physically* atomic block: its body counts as one machine step however many
   statements it contains. Trusted -- Raven has no scheduler to enforce it. Not
   to be confused with the `atomic` modifier on a contract, which states the
   *logical* atomicity of a callable and is checked. *)
atomic_block:
| ATOMIC; LBRACE; stmts = list(stmt); RBRACE {
  [Stmt.mk_block ~kind:Stmt.Atomic (List.flatten stmts)]
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
  let cond =
    Stmt.{ cond_test = Some e;
           cond_then = Stmt.mk_block_stmt ~loc:(Loc.make $startpos(st) $endpos(st)) st;
           cond_else = mk_skip ~loc:(Loc.make $endpos $endpos);
           cond_if_assumes_false = false;
         }
  in
  [Stmt.(Cond cond)]
}
;

if_then_else_stmt:
| IF; LPAREN; e = expr; RPAREN; st = stmt_no_short_if; ELSE; se = stmt { 
  let cond =
    Stmt.{ cond_test = Some e;
           cond_then = st;
           cond_else = Stmt.mk_block_stmt ~loc:(Loc.make $startpos(se) $endpos(se)) se;
           cond_if_assumes_false = false;
         }
  in
  [Stmt.(Cond cond)]
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
  [Stmt.(Cond cond)]
}
;
  
while_stmt:
| WHILE; LPAREN; e = expr; RPAREN; cs = loop_contract_list; s = block {
  let loop_contract, loop_contract_ext = cs in
  let loop =
    Stmt.{ loop_contract;
           loop_contract_ext;
           loop_prebody = mk_skip ~loc:(Loc.make $startpos $startpos);
           loop_test = e;
           loop_postbody = { stmt_desc = s; stmt_loc = Loc.make $startpos(s) $endpos(s) };
         }
  in
  [Stmt.Loop loop]
}
| WHILE; LPAREN; e = expr; RPAREN; s = stmt {
  let loop =
    Stmt.{ loop_contract = [];
           loop_contract_ext = [];
           loop_prebody = mk_skip ~loc:(Loc.make $startpos $startpos);
           loop_test = e;
           loop_postbody = Stmt.mk_block_stmt ~loc:(Loc.make $startpos(s) $endpos(s)) s;
         }
  in
  [Stmt.Loop loop]
}
;

while_stmt_no_short_if:
| WHILE; LPAREN; e = expr; RPAREN; s = stmt_no_short_if {
  let loop =
    Stmt.{ loop_contract = [];
           loop_contract_ext = [];
           loop_prebody = mk_skip ~loc:(Loc.make $startpos $startpos);
           loop_test = e;
           loop_postbody = s;
         }
  in
  [Stmt.Loop loop]
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
           spec_source = None; spec_trigs = [];
         }
  in
  `Invariant spec
}
| ce = contract_ext { `Ext ce }
;

(** Expressions *)

primary:
| c = CONSTVAL { Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) c []) }
| LPAREN; es = separated_list(COMMA, expr); RPAREN {
  Expr.mk_tuple ~loc:(Loc.make $symbolstartpos $endpos) es
}
| LPAREN; e = expr; COLON; t = type_expr; RPAREN {
  Expr.set_type_annot e (Some t)
}
| e = compr_expr { e }
| e = dot_expr { e }
| e = own_expr { e }
| e = au_expr { e }
| e = choose_expr { e }
;

(* %public so that an extension can add literals of its own, see seqExt_parser.mly. *)
%public compr_expr:
| LBRACEPIPE; es = separated_list(COMMA, expr); RBRACEPIPE {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Setenum es)
  }
| LBRACEPIPE; v = bound_var; COLONCOLON; e = expr; RBRACEPIPE {
    Expr.(mk_binder ~loc:(Loc.make $symbolstartpos $endpos) ~typ:Type.(mk_set (Loc.make $symbolstartpos $endpos) bot) Compr [v] e)
  }
;
  
dot_expr:
(*| MAP LT var_type, var_type GT LPAREN expr_list_opt RPAREN {*)
| p = qual_ident_expr; co = call_opt { co p }
;

own_expr:
| OWN; LPAREN; es = expr_list; RPAREN {
  Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Own es)
}

choose_expr:
| CHOOSE; LPAREN; e = expr; RPAREN {
  Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Choose [e])
}

(*cas_expr:
| CAS; LPAREN; es = expr_list; RPAREN {
  Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Cas es)
}*)

au_expr:
| AU; LT; qid = qual_ident; GT; LPAREN; es = expr_list; RPAREN {
  Expr.(mk_app ~typ:Type.perm ~loc:(Loc.make $symbolstartpos $endpos) (AUPred (Expr.to_qual_ident qid)) es)
}
| AUCOMMIT LT qid=qual_ident GT LPAREN es=expr_list; RPAREN {
  Expr.(mk_app ~typ:Type.perm ~loc:(Loc.make $symbolstartpos $endpos) (AUPredCommit (Expr.to_qual_ident qid)) es)
}

call_expr:
| p = qual_ident_expr; es = call {
  Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) (Expr.Var (Expr.to_qual_ident p)) es)
}
  
call:
| LPAREN; es = separated_list(COMMA, call_arg); RPAREN { es }

(* A call argument, optionally annotated with a type (`f(e: T)`) without needing
   the extra parens the standalone `(e: T)` form (see `primary`) would require. *)
call_arg:
| e = expr { e }
| e = expr; COLON; t = type_expr { Expr.set_type_annot e (Some t) }
  
call_opt:
| es = call { 
  fun p ->
    let p_ident = Expr.to_qual_ident p in
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.merge (to_loc p) (Loc.make $symbolstartpos $endpos)) (Var p_ident) es)
}
| (* empty *) { fun e -> e }
  
qual_ident_expr:
| x = qual_ident { x }
| p = primary DOT x = qual_ident {
  Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Read [p; x])
}
| p = primary DOT LPAREN x = qual_ident RPAREN {
  Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Read [p; x])
}

%public qual_ident:
| x = ident { x }
| m = mod_ident; DOT; x = IDENT {
  Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) (Var (QualIdent.append m x)) [])
}
| m = mod_ident; DOT; CHOOSE {
  let x = Ident.make (Loc.make $startpos($3) $endpos($3)) "choose" 0 in
  Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) (Var (QualIdent.append m x)) [])
}
 
mod_ident:
| x = MODIDENT { QualIdent.from_ident x}
| x = mod_ident; DOT; y = MODIDENT { QualIdent.append x y}

(* Any name a `func`/`pred`/`proc`/... or a `data` constructor can be declared
   with: an ordinary identifier, or one of the operator-shaped tokens Phase 1
   makes declarable, reached via `right_assoc_binary_op_ident` for `::` (a
   *reserved* string in Terminals.operator_table, unlike the rest -- carved out
   specifically because, unlike `+`/`==`/etc., it was never a closed Expr.constr
   case with hardcoded builtin semantics; see Library.List's own `::` constructor,
   lib/library/base_types.rav). No other reserved operator is made declarable at
   all, that being the separate, larger "reserved-operator overloading" feature
   this stops short of. *)
%public decl_name:
| x = IDENT { x }
| x = MULTOPSYM { x }
| x = ADDOPSYM { x }
| x = right_assoc_binary_op_ident { x }
| x = RELOPSYM { x }
| x = EQOPSYM { x }
| x = ANDOPSYM { x }
| x = OROPSYM { x }
;

(* The name of a function, predicate or procedure. `choose` is reserved for the `choose(e)`
   expression, but may still name a callable, such as `Library.Sets.choose`, which is
   then called qualified, as in `S.choose(s)`. *)
callable_name:
| x = decl_name { x }
| CHOOSE { Ident.make (Loc.make $startpos $endpos) "choose" 0 }

%public ident:
| x = decl_name {
  Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) (Var (QualIdent.from_ident x)) []) }
;

lookup_or_update_expr:
| e = primary; cont = lookup_or_update_opt { cont e }

(*
lookup_expr:
| e1 = qual_ident_expr; e_fn = lookup; { e_fn e1 }
| LPAREN; e1 = expr; RPAREN; e_fn = lookup; { e_fn e1 }*)

(* %public so that an extension can add forms of its own, see seqExt_parser.mly. *)
%public lookup_or_update_opt:
| (* empty *) { fun p -> p }
| LBRACKET; e2 = expr; COLONEQ; e3 = expr; RBRACKET cont = lookup_or_update_opt {
  fun e ->
    let e_upd =
      Expr.(mk_app ~typ:Type.any ~loc:(Loc.merge (to_loc e) (Loc.make $symbolstartpos $endpos)) MapUpdate [e; e2; e3])
    in
    cont e_upd
}
| LBRACKET; e2 = expr; RBRACKET cont = lookup_or_update_opt {
  fun e1 ->
    let e1_lookup = Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) MapLookUp [e1; e2]) in
    cont e1_lookup
}
| n = HASH {
  let e2 = Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $startpos(n) $endpos(n)) (Expr.Int n) []) in
  fun e1 -> Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) TupleLookUp [e1; e2])
}

  
%public unary_expr:
| e = lookup_or_update_expr { e }
(*| e = ident { e }*)
| MINUS; e = unary_expr {
  Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Uminus [e]) }
| e = unary_expr_not_plus_minus { e }
;

unary_expr_not_plus_minus:
| NOT; e = unary_expr  { Expr.mk_app ~loc:(Loc.make $symbolstartpos $endpos) ~typ:Type.any Expr.Not [e] }
;

mult_op:
| op = MULTOP { op }
| op = MULTOPSYM { Expr.Var (QualIdent.from_ident op) }

mult_expr:
| e = unary_expr { e }
| e1 = mult_expr; op = mult_op; e2 = unary_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) op [e1; e2])
  }
;

add_op:
| op = ADDOP { op }
| MINUS { Expr.Minus }
| op = ADDOPSYM { Expr.Var (QualIdent.from_ident op) }

add_expr:
| e = mult_expr { e }
| e1 = add_expr; op = add_op; e2 = mult_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) op [e1; e2])
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
| op = right_assoc_binary_op_ident { Expr.Var (QualIdent.from_ident op) }

right_assoc_binary_op_expr:
| e = add_expr { e }
| e1 = add_expr; op = right_assoc_binary_op; e2 = right_assoc_binary_op_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) op [e1; e2])
}
    
%public rel_expr:
| c = comp_seq {
  match c with
  | e, [] -> e
  | _, comps -> Base.List.reduce_exn comps ~f:(fun e1 e2 -> Expr.mk_and ~loc:(Loc.merge (Expr.to_loc e1) (Expr.to_loc e2)) [e1; e2])
}
| e1 = rel_expr; IN; e2 = right_assoc_binary_op_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Elem [e1; e2])
  } 
| e1 = rel_expr; NOTIN; e2 = right_assoc_binary_op_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Not [mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Elem [e1; e2]]) 
  }
;

comp_op:
| LT { Lt }
| GT { Gt }
| LEQ { Leq }
| GEQ { Geq }
| SUBSETEQ { Subseteq }
| op = RELOPSYM { Expr.Var (QualIdent.from_ident op) }
;

comp_seq:
| e = right_assoc_binary_op_expr { (e, []) }
| e1 = right_assoc_binary_op_expr; op = comp_op; cseq = comp_seq {
  let e2, comps = cseq in
  let loc1 = Expr.to_loc e1 in
  let loc2 = Expr.to_loc e2 in
  (e1, Expr.(mk_app ~typ:Type.any ~loc:(Loc.merge loc1 loc2) op [e1; e2]) :: comps)
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
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Eq [e1; e2])
  }
| e1 = eq_expr; NEQ; e2 = eq_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Not [mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Eq [e1; e2]])
  }
| e1 = eq_expr; op = EQOPSYM; e2 = eq_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) (Var (QualIdent.from_ident op)) [e1; e2])
  }
;

and_expr:
| e = eq_expr { e }
| e1 = and_expr; AND; e2 = eq_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) And [e1; e2])
  }
| e1 = and_expr; op = ANDOPSYM; e2 = eq_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) (Var (QualIdent.from_ident op)) [e1; e2])
  }
;

or_expr:
| e = and_expr { e }
| e1 = or_expr; OR; e2 = and_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Or [e1; e2])
  }
| e1 = or_expr; op = OROPSYM; e2 = and_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) (Var (QualIdent.from_ident op)) [e1; e2])
  }
;



impl_expr:
| e = or_expr { e }
| e1 = or_expr; IMPLIES; e2 = impl_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Impl [e1; e2])
  }
;

iff_expr:
| e = impl_expr { e }
| e1 = iff_expr IFF e2 = iff_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Eq [e1; e2])
  }
;

(* Right-associative: `a ? b : c ? d : e` is `a ? b : (c ? d : e)`. *)
ite_expr:
| e = iff_expr { e }
| e1 = iff_expr; QMARK; e2 = ite_expr; COLON; e3 = ite_expr {
    Expr.(mk_app ~typ:Type.any ~loc:(Loc.make $symbolstartpos $endpos) Ite [e1; e2; e3])
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
             var_loc = Loc.make $symbolstartpos $endpos;
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
           var_type = Type.mk_any Loc.dummy;
           var_loc = Loc.make $symbolstartpos $endpos;
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
           var_loc = Loc.make $symbolstartpos $endpos;
           var_const = true;
           var_ghost = false;
           var_implicit = false;
         }
  in
  decl
} 
;

%public type_expr:
| ct = CONSTTYPE { Type.mk_app ~loc:(Loc.make $symbolstartpos $endpos) ct [] }
| ATOMICTOKEN LT qid = qual_ident GT { Type.mk_atomic_token (Loc.make $symbolstartpos $endpos) (Expr.to_qual_ident qid) }
//| x = IDENT { Type.mk_var (QualIdent.from_ident x) }
| ct = TYPECONSTR LBRACKET ts = separated_list(COMMA, type_expr) RBRACKET {
  let loc = Loc.make $symbolstartpos $endpos in
  if List.length ts <> snd ct then
    Error.syntax_error loc (Printf.sprintf "This type constructor expects %d argument(s)" (snd ct))
  else begin
    match ct, ts with
    | (Type.Map, 1), [t] ->
        Type.mk_set loc t
    | (c, _), _ -> Type.mk_app ~loc c ts
  end
  }
| x = mod_ident { Type.mk_var x }
| LPAREN ts = separated_list(COMMA, type_expr) RPAREN { Type.mk_prod (Loc.make $symbolstartpos $endpos) ts }
| x = mod_ident LBRACKET; ts = type_expr_list; RBRACKET {
  Type.(App(Var x, ts, Type.mk_attr (Loc.make $symbolstartpos $endpos))) }
    
  
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
    Expr.(mk_binder ~loc:(Loc.make $symbolstartpos $endpos) ~trigs q vs e)
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
