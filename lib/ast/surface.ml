(** Builders of programs as the parser produces them, before type checking: the parser
    builds its output with them, and so can other front ends. Types not given are left to
    the type checker ([Type.any]), and locations are those of the source. *)

open Base
open Util
open AstDef

module Type = struct
  type t = Type.t
  type var_decl = Type.var_decl

  let constant ~loc (c : Type.constr) : t = Type.mk_app ~loc c []
  let int ~loc = constant ~loc Int
  let bool ~loc = constant ~loc Bool
  let real ~loc = constant ~loc Real
  let ref ~loc = constant ~loc Ref
  let perm ~loc = constant ~loc Perm

  (** A type left to the type checker. *)
  let any ~loc = Type.mk_any loc

  let map ~loc key value : t = Type.mk_app ~loc Map [ key; value ]
  let set ~loc elem : t = Type.mk_set loc elem
  let fin_set ~loc elem : t = Type.mk_app ~loc FinSet [ elem ]

  (** The type constructor [c] of the given arity applied to [args], as in [Map[K, V]];
      [Set[T]] is [Map[T, Bool]]. *)
  let constr ~loc ((c, arity) : Type.constr * int) (args : t list) : t =
    if List.length args <> arity then
      Error.syntax_error loc
        (Printf.sprintf "This type constructor expects %d argument(s)" arity)
    else
      match (c, args) with
      | Map, [ elem ] when arity = 1 -> set ~loc elem
      | _ -> Type.mk_app ~loc c args

  let tuple ~loc (ts : t list) : t = Type.mk_prod loc ts

  (** The type or module [name], applied to [args] if any, as in [Seq[Int]]. *)
  let named ~loc (name : QualIdent.t) (args : t list) : t =
    match args with [] -> Type.mk_var name | _ -> App (Var name, args, Type.mk_attr loc)

  let atomic_token ~loc (proc : QualIdent.t) : t = Type.mk_atomic_token loc proc

  (** The data type with [variants], as in [data { case nil case cons(hd: Int, tl: T) }].
  *)
  let data ~loc (variants : Type.variant_decl list) : t =
    Type.mk_data (QualIdent.from_ident (Ident.make Loc.dummy "" 0)) variants loc

  let variant ~loc (name : Ident.t) (args : Type.var_decl list) : Type.variant_decl =
    { variant_name = name; variant_loc = loc; variant_args = args }

  (** The declaration of [name] of type [typ], as of a parameter or bound variable. *)
  let var_decl ~loc ?(ghost = false) ?(implicit = false) ?(const = false) (name : Ident.t)
      (typ : t) : Type.var_decl =
    {
      var_name = name;
      var_type = (if ghost then Type.set_ghost true typ else typ);
      var_loc = loc;
      var_const = const;
      var_ghost = ghost;
      var_implicit = implicit;
    }

  (** [decl] as a parameter or result that is ghost and implicit as given. *)
  let with_modifiers ~ghost ~implicit (decl : var_decl) : var_decl =
    {
      decl with
      var_type = decl.var_type |> Type.set_ghost ghost;
      var_ghost = ghost;
      var_implicit = implicit;
    }

  (** The declaration of [name], of type [typ] if given, of a local or constant. *)
  let local_decl ~loc (name : Ident.t) (typ : t option) : Type.var_decl =
    var_decl ~loc ~const:true name (Option.value typ ~default:(any ~loc:Loc.dummy))
end

module Expr = struct
  type t = Expr.t

  (** The binary operators: those of the language, and user-defined symbolic ones. *)
  type binop =
    | Mult
    | Div
    | Mod
    | Plus
    | Minus
    | Lt
    | Leq
    | Gt
    | Geq
    | Eq
    | Neq
    | Iff
    | And
    | Or
    | Impl
    | In
    | Not_in
    | Union
    | Inter
    | Diff
    | Subseteq
    | User of Ident.t

  let app ~loc (c : Expr.constr) (args : t list) : t =
    Expr.mk_app ~typ:AstDef.Type.any ~loc c args

  (** A literal such as [1], [2.5], [true] or [null]. *)
  let constant ~loc (c : Expr.constr) : t = app ~loc c []

  let int ~loc n = constant ~loc (Int (Int64.of_int n))
  let real ~loc r = constant ~loc (Real r)
  let bool ~loc b = constant ~loc (Bool b)
  let null ~loc = constant ~loc Null
  let var ~loc (name : QualIdent.t) : t = app ~loc (Var name) []
  let ident ~loc (name : Ident.t) : t = var ~loc (QualIdent.from_ident name)
  let tuple ~loc (es : t list) : t = Expr.mk_tuple ~loc es

  (** [e] annotated with the type [typ], as in [(e: T)]. *)
  let annotated (e : t) (typ : Type.t) : t = Expr.set_type_annot e (Some typ)

  (** The call of the function, predicate or constructor [callee] with [args]. *)
  let call ~loc (callee : QualIdent.t) (args : t list) : t = app ~loc (Var callee) args

  (** The field [field] of [e], as in [e.f]. [field_loc] is that of the field's name. *)
  let field ~loc ?field_loc (e : t) (field : QualIdent.t) : t =
    let field_loc = Option.value field_loc ~default:(QualIdent.to_loc field) in
    app ~loc Read [ e; var ~loc:field_loc field ]

  let own ~loc (args : t list) : t = app ~loc Own args

  let au ~loc (proc : QualIdent.t) (args : t list) : t =
    Expr.mk_app ~typ:AstDef.Type.perm ~loc (AUPred proc) args

  let au_commit ~loc (proc : QualIdent.t) (args : t list) : t =
    Expr.mk_app ~typ:AstDef.Type.perm ~loc (AUPredCommit proc) args

  (** The enumeration [opener e1, ..., en closer], as the set [{e1, ..., en}] for the
      opener ["{"] and the sequence [[e1, ..., en]] for ["["]. *)
  let enumeration ~loc (opener : string) (es : t list) : t =
    app ~loc (Enumeration opener) es

  let set ~loc es = enumeration ~loc "{" es
  let seq ~loc es = enumeration ~loc "[" es

  (** The set comprehension [{x: T :: e}]. *)
  let set_compr ~loc (var : Type.var_decl) (e : t) : t =
    Expr.mk_binder ~loc ~typ:(AstDef.Type.mk_set loc AstDef.Type.bot) Compr [ var ] e

  (** The map literal [{k1 := v1, ..., else default}]: updates of the constant map of
      [default], whose key type comes from the keys or the expected type. *)
  let map_literal ~loc (entries : (t * t) list) (default : t) : t =
    let key =
      Type.var_decl ~loc (Ident.make loc Expr.map_literal_key 0) (Type.any ~loc)
    in
    let constant = Expr.mk_binder ~loc ~typ:AstDef.Type.any Compr [ key ] default in
    List.fold entries ~init:constant ~f:(fun map (k, v) ->
        app ~loc MapUpdate [ map; k; v ])

  (** The mixfix operator [name] applied to [base] and [bounds], as [_[_]] in [e[i]]; the
      call's location spans from [base]. *)
  let mixfix ~loc (name : string) (base : t) (bounds : t list) : t =
    let loc = Loc.merge (Expr.to_loc base) loc in
    call ~loc (QualIdent.from_ident (Ident.make loc name 0)) (base :: bounds)

  let index ~loc e i = mixfix ~loc "_[_]" e [ i ]
  let update ~loc e i v = mixfix ~loc "_[_:=_]" e [ i; v ]
  let slice_from ~loc e lo = mixfix ~loc "_[_..]" e [ lo ]
  let slice_to ~loc e hi = mixfix ~loc "_[.._]" e [ hi ]
  let slice ~loc e lo hi = mixfix ~loc "_[_.._]" e [ lo; hi ]

  (** The component [n] of the tuple [e], as in [e#n]. *)
  let tuple_get ~loc ?index_loc (e : t) (n : int) : t =
    let index_loc = Option.value index_loc ~default:loc in
    app ~loc TupleLookUp [ e; int ~loc:index_loc n ]

  let neg ~loc e = app ~loc Uminus [ e ]
  let not_ ~loc e = app ~loc Not [ e ]

  (** [e1 op e2]. [op_loc] is that of the operator, for those that name a function. *)
  let binary ~loc ?op_loc (op : binop) (e1 : t) (e2 : t) : t =
    let named name =
      Expr.Var
        (QualIdent.from_ident (Ident.make (Option.value op_loc ~default:loc) name 0))
    in
    let apply c = app ~loc c [ e1; e2 ] in
    match op with
    | Mult -> apply Mult
    | Div -> apply Div
    | Mod -> apply Mod
    | Plus -> apply Plus
    | Minus -> apply Minus
    | Gt -> apply Gt
    | Geq -> apply Geq
    | Eq | Iff -> apply Eq
    | Neq -> not_ ~loc (apply Eq)
    | And -> apply And
    | Or -> apply Or
    | Impl -> apply Impl
    | Lt -> apply (named "<")
    | Leq -> apply (named "<=")
    | In -> apply (named "in")
    | Not_in -> not_ ~loc (apply (named "in"))
    | Union -> apply (named "++")
    | Inter -> apply (named "**")
    | Diff -> apply (named "--")
    | Subseteq -> apply (named "subseteq")
    | User name -> apply (Var (QualIdent.from_ident name))

  (** The conjunction of [es], as of a chain of comparisons [a < b <= c]. *)
  let conj ~loc (es : t list) : t = Expr.mk_and ~loc es

  let ite ~loc c e1 e2 = app ~loc Ite [ c; e1; e2 ]

  (** The quantifier [q] over [vars], with [triggers], of [body]. *)
  let quant ~loc ?(triggers = []) (q : Expr.binder) (vars : Type.var_decl list) (body : t)
      : t =
    Expr.mk_binder ~loc ~trigs:triggers q vars body

  let forall ~loc ?triggers vars body = quant ~loc ?triggers Forall vars body
  let exists ~loc ?triggers vars body = quant ~loc ?triggers Exists vars body
end

module Stmt = struct
  type t = Stmt.t

  (** The statement [desc] at [loc]. *)
  let at ~loc (desc : Stmt.stmt_desc) : t = { stmt_desc = desc; stmt_loc = loc }

  (** The specification [e], optionally named and atomic, of an assertion or contract. *)
  let spec ?atomic ?name (e : Expr.t) : Stmt.spec = Stmt.mk_spec ?atomic ?name e

  (** A contract clause with [triggers], as of [ensures {t} e]. *)
  let spec_with_triggers ~atomic ~(triggers : Expr.t list list) (e : Expr.t) : Stmt.spec =
    { (Stmt.mk_spec ~atomic e) with spec_trigs = triggers }

  let block (stmts : t list) : Stmt.stmt_desc = Stmt.mk_block stmts
  let ghost_block (stmts : t list) : Stmt.stmt_desc = Stmt.mk_block ~kind:Ghost stmts
  let atomic_block (stmts : t list) : Stmt.stmt_desc = Stmt.mk_block ~kind:Atomic stmts

  (** [stmts] as a block at [loc]. *)
  let block_stmt ~loc (stmts : t list) : t = Stmt.mk_block_stmt ~loc stmts

  let skip ~loc : t = Stmt.mk_skip ~loc

  (** A call as a statement, as in [f(x);]. *)
  let call (e : Expr.t) : Stmt.stmt_desc =
    Basic (Assign { assign_lhs = []; assign_rhs = e; assign_is_init = false })

  let spawn (callee : QualIdent.t) (args : Expr.t list) : Stmt.stmt_desc =
    Basic
      (Call
         {
           call_lhs = [];
           call_name = callee;
           call_args = args;
           call_is_spawn = true;
           call_is_init = false;
           call_precond_given = false;
         })

  (** The variable among [lhs], which are expressions as written on the left of [:=] or
      [:|]. *)
  let local_target ~(error : string) (e : Expr.t) : QualIdent.t =
    match e with
    | App (Var qual_ident, [], _) when QualIdent.is_local qual_ident -> qual_ident
    | e -> Error.syntax_error (AstDef.Expr.to_loc e) error

  (** The indexed assignment [x[i] := v] is [x := x[i := v]], and [x[i][j] := v] is
      [x := x[i := x[i][j := v]]]. The type checker gives it its meaning: an update of a
      map, or whatever an extension claims it to be. *)
  let rec index_assign (base : Expr.t) (index : Expr.t) (value : Expr.t) :
      Stmt.basic_stmt_desc =
    let loc = Loc.merge (AstDef.Expr.to_loc base) (AstDef.Expr.to_loc value) in
    let update =
      Expr.mixfix ~loc:(AstDef.Expr.to_loc base) "_[_:=_]" base [ index; value ]
    in
    let update = AstDef.Expr.set_loc update loc in
    match base with
    | App (Var qual_ident, [], _) when QualIdent.is_local qual_ident ->
        Stmt.Assign
          { assign_lhs = [ qual_ident ]; assign_rhs = update; assign_is_init = false }
    | App (MapLookUp, [ base'; index' ], _) -> index_assign base' index' update
    | App (Var name, [ base'; index' ], _)
      when QualIdent.is_local name
           && String.equal (Ident.name (QualIdent.unqualify name)) "_[_]" ->
        index_assign base' index' update
    | _ ->
        Error.syntax_error (AstDef.Expr.to_loc base)
          "Expected a variable, possibly indexed, on the left-hand side of an indexed \
           assignment"

  type rhs = Expr.t list * bool -> Stmt.stmt_desc * Expr.t option
  (** The right-hand side of an assignment, applied to its targets, as written, and to
      whether it initializes them: the statement, and for a definition, an initial value
      if the statement is not a plain assignment. Extensions add right-hand sides of their
      own. *)

  (** The right-hand side [e]: a field write if the target is a field, an indexed
      assignment if it is indexed, and an assignment of variables otherwise. *)
  let expr_rhs (e : Expr.t) : rhs = function
    | [ App (Read, [ field_write_ref; App (Var field_write_field, [], _) ], _) ], _ ->
        ( Basic (FieldWrite { field_write_ref; field_write_field; field_write_val = e }),
          None )
    | [ App (MapLookUp, [ base; index ], _) ], _ ->
        (Basic (index_assign base index e), None)
    | [ App (Var name, [ base; index ], _) ], _
      when QualIdent.is_local name
           && String.equal (Ident.name (QualIdent.unqualify name)) "_[_]" ->
        (Basic (index_assign base index e), None)
    | es, assign_is_init ->
        let vs =
          List.map es
            ~f:
              (local_target
                 ~error:
                   "Expected a single field location, a single indexed location, or \
                    local variables on left-hand side of assignment")
        in
        (Basic (Assign { assign_lhs = vs; assign_rhs = e; assign_is_init }), None)

  (** The allocation [new(f1: e1, ..., fn)], of the fields with their initial values if
      given. *)
  let new_rhs (fields : (QualIdent.t * Expr.t option) list) : rhs = function
    | [ App (Var x, _, _) ], assign_is_init ->
        ( Basic (New { new_lhs = x; new_args = fields; new_is_init = assign_is_init }),
          Some (AstDef.Expr.mk_null ()) )
    | es, _ ->
        Error.syntax_error
          (es |> List.hd_exn |> AstDef.Expr.to_loc)
          "Result of allocation must be assigned to a single variable"

  (** The assignment [e1, ..., en := rhs]. *)
  let assign (lhs : Expr.t list) (rhs : rhs) : Stmt.stmt_desc = fst (rhs (lhs, false))

  (** The binding [x1, ..., xn :| e] of the variables to values satisfying [e]. *)
  let bind (lhs : Expr.t list) (e : Expr.t) : Stmt.stmt_desc =
    let vs =
      List.map lhs
        ~f:
          (local_target
             ~error:
               "Expected single field location or local variables on left-hand side of \
                assignment")
    in
    Basic (Bind { bind_lhs = vs; bind_rhs = Stmt.mk_spec e })

  let havoc (x : QualIdent.t) : Stmt.stmt_desc =
    Basic (Havoc { havoc_var = x; havoc_is_init = false })

  (** The assertion, assumption, inhale or exhale [spec]. *)
  let spec_stmt (kind : Stmt.spec_kind) (spec : Stmt.spec) : Stmt.stmt_desc =
    Basic (Spec (kind, spec))

  (** [return e1, ..., en], of a tuple if there are several values. *)
  let return ~loc (es : Expr.t list) : Stmt.stmt_desc =
    let e = match es with [ e ] -> e | es -> AstDef.Expr.mk_tuple ~loc es in
    Basic (Return e)

  (** [fold p(args)] or [unfold p(args)], with witnesses or bindings [x := e] of the
      predicate's existentials. *)
  let use (kind : Stmt.use_kind) (name : QualIdent.t) ?(witnesses = [])
      (args : Expr.t list) : Stmt.stmt_desc =
    Basic
      (Use
         {
           use_kind = kind;
           use_name = name;
           use_args = args;
           use_witnesses_or_binds = witnesses;
           use_spec_error = [];
         })

  let if_ ~(then_loc : Loc.t) ~(else_loc : Loc.t) (test : Expr.t) (then_ : t list)
      (else_ : t list) : Stmt.stmt_desc =
    Cond
      {
        cond_test = Some test;
        cond_then = Stmt.mk_block_stmt ~loc:then_loc then_;
        cond_else = Stmt.mk_block_stmt ~loc:else_loc else_;
        cond_if_assumes_false = false;
      }

  (** [if (test) then_ else else_], of branches that are statements already. *)
  let cond (test : Expr.t) (then_ : t) (else_ : t) : Stmt.stmt_desc =
    Cond
      {
        cond_test = Some test;
        cond_then = then_;
        cond_else = else_;
        cond_if_assumes_false = false;
      }

  (** [while (test) invariant ... body], at [loc]. *)
  let while_ ~loc ?(invariants = []) ?(contract_ext = []) (test : Expr.t) (body : t) :
      Stmt.stmt_desc =
    Loop
      {
        loop_contract = invariants;
        loop_contract_ext = contract_ext;
        loop_prebody = Stmt.mk_skip ~loc:(Loc.to_start loc);
        loop_test = test;
        loop_postbody = body;
      }

  (** A local variable definition, followed by the statement assigning its initial value,
      if any. *)
  let local_var_def ~ghost ~const (decl : Type.var_decl) (rhs : rhs option) ~rhs_loc :
      Stmt.stmt_desc list =
    let decl =
      {
        decl with
        var_type = decl.var_type |> AstDef.Type.set_ghost ghost;
        var_ghost = ghost;
        var_const = const;
      }
    in
    match rhs with
    | Some rhs ->
        let stmt, default_expr_optn = rhs ([ AstDef.Expr.from_var_decl decl ], true) in
        let var_init =
          match (stmt, default_expr_optn) with
          | Stmt.Basic (Assign assign_desc), None -> Some assign_desc.assign_rhs
          | _, Some expr -> Some (AstDef.Expr.set_loc expr rhs_loc)
          | _ -> None
        in
        [
          Stmt.(Basic (VarDef { var_decl = decl; var_init; var_is_free = NotFree })); stmt;
        ]
    | None ->
        [
          Stmt.(
            Basic (VarDef { var_decl = decl; var_init = None; var_is_free = NotFree }));
        ]
end

module Callable = struct
  type t = Callable.t

  (** The declaration of a callable of [kind] named [name]: its parameters, of which
      [loc_params] name the fields of leading location parameters, its results and its
      contract. *)
  let decl ~loc ~(kind : Callable.call_kind) ?(is_inline = false) ?(formals = [])
      ?(returns = []) ?(precond = []) ?(postcond = []) ?(contract_ext = []) ?opens
      ?(loc_params = []) (name : Ident.t) : Callable.call_decl =
    let decl =
      Callable.mk_call_decl ~kind ~name ~loc ~formals ~returns ~precond ~postcond
        ~contract_ext ?opens ~loc_params ()
    in
    { decl with call_decl_is_inline = is_inline }

  (** The kinds of procedure-like callables. *)
  type proc_kind = Proc | Lemma of { is_auto : bool } | Axiom of { is_auto : bool }

  (** A procedure, lemma or axiom with [decl] and [body]; the results of a lemma are
      ghost. An axiom has no body. *)
  let proc (kind : proc_kind) (decl : Callable.call_decl) (body : Stmt.t option) : t =
    let call_decl_kind, call_decl_is_auto =
      match kind with
      | Proc -> (AstDef.Callable.Proc, false)
      | Lemma { is_auto } | Axiom { is_auto } -> (AstDef.Callable.Lemma, is_auto)
    in
    let ghostify (decls : Type.var_decl list) =
      List.map decls ~f:(fun decl ->
          {
            decl with
            var_ghost = true;
            var_type = AstDef.Type.set_ghost true decl.var_type;
          })
    in
    let call_decl_returns =
      match call_decl_kind with
      | Lemma | Pred | Invariant -> ghostify decl.call_decl_returns
      | Proc | Func -> decl.call_decl_returns
    in
    {
      call_decl = { decl with call_decl_kind; call_decl_is_auto; call_decl_returns };
      call_def = ProcDef { proc_body = body };
    }

  (** A function, predicate or invariant with [decl] and [body]; the results of a
      predicate or invariant are implicit ghosts. *)
  let func (decl : Callable.call_decl) (body : Expr.t option) : t =
    let implicify (decls : Type.var_decl list) =
      List.map decls ~f:(fun decl ->
          {
            decl with
            var_ghost = true;
            var_implicit = true;
            var_type = AstDef.Type.set_ghost true decl.var_type;
          })
    in
    let call_decl_returns =
      match decl.call_decl_kind with
      | Pred | Invariant -> implicify decl.call_decl_returns
      | Proc | Lemma | Func -> decl.call_decl_returns
    in
    {
      call_decl = { decl with call_decl_returns };
      call_def = FuncDef { func_body = body };
    }
end

module Module = struct
  type member = Module.module_instr

  (** The field [name] of type [typ]. *)
  let field ~loc ?(ghost = false) ~(type_loc : Loc.t) (name : Ident.t) (typ : Type.t) :
      Module.field_def =
    {
      field_name = name;
      field_type = AstDef.Type.mk_fld type_loc typ |> AstDef.Type.set_ghost ghost;
      field_is_ghost = ghost;
      field_alias = None;
      field_loc = loc;
    }

  (** The manifest field [name] denoting the field [target], as in [field f = M.g]. *)
  let field_alias ~loc ?(ghost = false) ~(type_loc : Loc.t) (name : Ident.t)
      (target : QualIdent.t) : Module.field_def =
    {
      field_name = name;
      field_type =
        AstDef.Type.mk_fld type_loc AstDef.Type.any |> AstDef.Type.set_ghost ghost;
      field_is_ghost = ghost;
      field_alias = Some target;
      field_loc = loc;
    }

  (** The type [name], defined as [def] if given, a representation type if [rep]. *)
  let type_def ~loc ?(rep = false) (name : Ident.t) (def : Type.t option) :
      Module.type_def =
    {
      type_def_name = name;
      type_def_expr = def;
      type_def_rep = rep;
      type_def_is_free = false;
      type_def_loc = loc;
    }

  (** The constant or variable member [decl], with its value if given. *)
  let var_def ~ghost ~const (decl : Type.var_decl) (init : Expr.t option) :
      AstDef.Stmt.var_def =
    {
      var_decl =
        {
          decl with
          var_type = decl.var_type |> AstDef.Type.set_ghost ghost;
          var_ghost = ghost;
          var_const = const;
        };
      var_init = init;
      var_is_free = NotFree;
    }

  (** [import name], or [import name._] of all members of the module [name] if [all]. *)
  let import ~loc ?(all = false) (name : QualIdent.t) : Module.import_directive =
    { import_name = name; import_all = all; import_prelude = false; import_loc = loc }

  (** The parameter [name : typ] of a functor. *)
  let param ~loc (name : Ident.t) (typ : QualIdent.t) : Module.module_inst =
    Module.mk_mod_inst ~name ~typ ~loc ()

  (** The argument of a module instantiation: a module if [typ] names one, a type
      otherwise. *)
  let arg (typ : Type.t) : Module.module_inst_arg =
    match typ with App (Var qi, [], _) -> ModArg qi | tp -> TypeArg tp

  (** The header of the module or interface [name]: its parameters and the interfaces it
      implements, sealed if [sealed]. *)
  let header ~loc ?(params = []) ?(implements = []) ?(sealed = false) (name : Ident.t) :
      Module.module_decl =
    {
      Module.empty_decl with
      mod_decl_name = name;
      mod_decl_formals = params;
      mod_decl_returns = implements;
      mod_decl_is_sealed = sealed;
      mod_decl_loc = loc;
    }

  (** The module, or the interface if [interface], with [header] and [members]. *)
  let module_def ?(interface = false) (header : Module.module_decl)
      (members : member list) : Module.symbol =
    ModDef
      { mod_decl = { header with mod_decl_is_interface = interface }; mod_def = members }

  (** The instance [module name : typ = def], or the abstract module [name : typ]. *)
  let instance ~loc ?def ?(interface = false) ?(sealed = false) (name : Ident.t)
      (typ : QualIdent.t) : Module.symbol =
    ModInst
      (Module.mk_mod_inst ~name ~typ ?def ~is_interface:interface ~is_sealed:sealed ~loc
         ())

  (** [symbol], as a member that is [free] if so. *)
  let symbol ?(free = false) (symbol : Module.symbol) : member =
    SymbolDef (if free then Symbol.set_free symbol else symbol)

  let import_member (import : Module.import_directive) : member = Import import

  (** A sealed module without parameters, [module M :> I { ... }], as the module
      [M$Impl : I] with its body and the sealed instance [module M :> I = M$Impl]. Other
      members are as they are. *)
  let expand_sealed (member : member) : member list =
    let open Module in
    match member with
    | SymbolDef (ModDef ({ mod_decl = decl; _ } as mod_def))
      when decl.mod_decl_is_sealed
           && List.is_empty decl.mod_decl_formals
           && not decl.mod_decl_is_interface -> (
        match decl.mod_decl_returns with
        | [ (iface, _) ] ->
            let loc = decl.mod_decl_loc in
            let impl_name =
              Ident.make loc (decl.mod_decl_name.ident_name ^ sealed_impl_suffix) 0
            in
            let impl =
              ModDef
                {
                  mod_def with
                  mod_decl =
                    { decl with mod_decl_name = impl_name; mod_decl_is_sealed = false };
                }
            in
            let view =
              ModInst
                (mk_mod_inst ~name:decl.mod_decl_name ~typ:iface
                   ~def:(QualIdent.from_ident impl_name, [])
                   ~is_sealed:true ~loc ())
            in
            [ SymbolDef impl; SymbolDef view ]
        | _ -> [ member ])
    | _ -> [ member ]

  (** The members, with sealed modules expanded. *)
  let members (ms : member list) : member list = List.concat_map ms ~f:expand_sealed

  (** The program with [members]. *)
  let program ~loc (members : member list) : Module.t =
    {
      mod_decl = { Module.empty_decl with mod_decl_name = Ident.make loc "$Program" 0 };
      mod_def = members;
    }
end
