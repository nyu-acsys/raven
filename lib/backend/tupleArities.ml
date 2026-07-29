(** Computes the set of tuple (SMT-LIB `$tuple_n`) arities actually needed to represent a
    checked program, so the backend can declare exactly those sorts instead of an arbitrary
    fixed range. See lib/backend/smt_solver.ml for where the declarations happen. *)

open Base
open Ast
open Util

let empty_arities = Set.empty (module Int)

let rec type_arities (tp : Type.t) : Set.M(Int).t =
  match tp with
  | App (Prod, ts, _) ->
      List.fold ts
        ~init:(Set.add empty_arities (List.length ts))
        ~f:(fun acc t -> Set.union acc (type_arities t))
  | App (Data (_, variant_decls), ts, _) ->
      let acc =
        List.fold ts ~init:empty_arities ~f:(fun acc t ->
            Set.union acc (type_arities t))
      in
      List.fold variant_decls ~init:acc ~f:(fun acc variant_decl ->
          List.fold variant_decl.Type.variant_args ~init:acc
            ~f:(fun acc arg -> Set.union acc (type_arities arg.Type.var_type)))
  | App (_, ts, _) ->
      List.fold ts ~init:empty_arities ~f:(fun acc t ->
          Set.union acc (type_arities t))

let rec expr_arities (e : Expr.t) : Set.M(Int).t =
  let acc = type_arities (Expr.to_type e) in
  match e with
  | App (_, ts, _) ->
      List.fold ts ~init:acc ~f:(fun acc e -> Set.union acc (expr_arities e))
  | Binder (_, vs, trgs, body, _) ->
      let acc =
        List.fold vs ~init:acc ~f:(fun acc vd ->
            Set.union acc (type_arities vd.Type.var_type))
      in
      let acc =
        List.fold trgs ~init:acc ~f:(fun acc es ->
            List.fold es ~init:acc ~f:(fun acc e ->
                Set.union acc (expr_arities e)))
      in
      Set.union acc (expr_arities body)

let exprs_arities (es : Expr.t list) : Set.M(Int).t =
  List.fold es ~init:empty_arities ~f:(fun acc e ->
      Set.union acc (expr_arities e))

let rec stmt_arities (s : Stmt.t) : Set.M(Int).t =
  match s.stmt_desc with
  | Block b ->
      List.fold b.block_body ~init:empty_arities ~f:(fun acc s ->
          Set.union acc (stmt_arities s))
  | Basic bs -> basic_stmt_arities bs
  | Loop l ->
      let acc = expr_arities l.loop_test in
      let acc =
        List.fold l.loop_contract ~init:acc ~f:(fun acc spec ->
            Set.union acc (expr_arities spec.Stmt.spec_form))
      in
      let acc = Set.union acc (stmt_arities l.loop_prebody) in
      Set.union acc (stmt_arities l.loop_postbody)
  | Cond c ->
      let acc =
        match c.cond_test with None -> empty_arities | Some e -> expr_arities e
      in
      let acc = Set.union acc (stmt_arities c.cond_then) in
      Set.union acc (stmt_arities c.cond_else)
  | StmtExt _ ->
      Error.internal_error s.stmt_loc
        "unexpected statement extension: should have been rewritten away before the backend"

and basic_stmt_arities (bs : Stmt.basic_stmt_desc) : Set.M(Int).t =
  match bs with
  | VarDef vd ->
      let acc = type_arities vd.var_decl.Type.var_type in
      (match vd.var_init with
      | None -> acc
      | Some e -> Set.union acc (expr_arities e))
  | Spec (_, spec) -> expr_arities spec.spec_form
  | New nd -> exprs_arities (List.filter_map nd.new_args ~f:snd)
  | Assign ad -> expr_arities ad.assign_rhs
  | Bind bd -> expr_arities bd.bind_rhs.spec_form
  | FieldRead frd -> expr_arities frd.field_read_ref
  | FieldWrite fwd ->
      exprs_arities [ fwd.field_write_ref; fwd.field_write_val ]
  | Havoc _ -> empty_arities
  | Call cd -> exprs_arities cd.call_args
  | Return e -> expr_arities e
  | Use ud ->
      let acc = exprs_arities ud.use_args in
      Set.union acc
        (exprs_arities (List.map ud.use_witnesses_or_binds ~f:snd))
  | AUAction ad -> (
      match ad.auaction_kind with
      | BindAU _ -> empty_arities
      | OpenAU o -> exprs_arities ((o.token :: o.lhs) @ o.proc_args)
      | AbortAU a -> exprs_arities (a.token :: a.proc_args)
      | CommitAU c -> exprs_arities ((c.token :: c.proc_args) @ c.proc_rets))
  | Fpu fd ->
      let acc = exprs_arities [ fd.fpu_ref; fd.fpu_new_val ] in
      (match fd.fpu_old_val with
      | None -> acc
      | Some e -> Set.union acc (expr_arities e))
  | BasicStmtExt (_, es) -> exprs_arities es

let var_decl_arities (vd : var_decl) : Set.M(Int).t = type_arities vd.var_type

let var_decls_arities (vds : var_decl list) : Set.M(Int).t =
  List.fold vds ~init:empty_arities ~f:(fun acc vd ->
      Set.union acc (var_decl_arities vd))

(** Tuple arity of the combined return value that [Backend.Checker] synthesizes for a
    [Func]/[Pred]/[Invariant] declaration (see [declare_fn] and [check_callable] in
    checker.ml) -- mirrors [Type.mk_prod]/[Expr.mk_tuple], which only actually build a
    tuple when there are 2 or more return values. *)
let return_tuple_arity (call_decl : Callable.call_decl) : Set.M(Int).t =
  match call_decl.call_decl_returns with
  | [] | [ _ ] -> empty_arities
  | returns -> Set.singleton (module Int) (List.length returns)

let call_decl_arities (call_decl : Callable.call_decl) : Set.M(Int).t =
  let acc =
    var_decls_arities
      (call_decl.call_decl_formals @ call_decl.call_decl_returns
     @ call_decl.call_decl_locals)
  in
  List.fold
    (call_decl.call_decl_precond @ call_decl.call_decl_postcond)
    ~init:acc
    ~f:(fun acc spec -> Set.union acc (expr_arities spec.Stmt.spec_form))

let symbol_arities (sym : Module.symbol) : Set.M(Int).t =
  match sym with
  | ModDef _ | ModInst _ ->
      (* Members are also registered individually, under their own fully qualified
         names, elsewhere in the symbol table. *)
      empty_arities
  | TypeDef td -> (
      match td.type_def_expr with
      | None -> empty_arities
      | Some tp -> type_arities tp)
  | ConstrDef cd ->
      Set.union (var_decls_arities cd.constr_args)
        (type_arities cd.constr_return_type)
  | DestrDef dd ->
      Set.union (type_arities dd.destr_arg) (type_arities dd.destr_return_type)
  | FieldDef fd -> type_arities fd.field_type
  | VarDef vd ->
      let acc = var_decl_arities vd.var_decl in
      (match vd.var_init with
      | None -> acc
      | Some e -> Set.union acc (expr_arities e))
  | CallDef c ->
      let acc = call_decl_arities c.call_decl in
      (match c.call_def with
      | FuncDef { func_body } ->
          let acc =
            match func_body with
            | None -> acc
            | Some e -> Set.union acc (expr_arities e)
          in
          Set.union acc (return_tuple_arity c.call_decl)
      | ProcDef { proc_body } -> (
          match proc_body with
          | None -> acc
          | Some s -> Set.union acc (stmt_arities s)))

let of_symbols (symbols : Module.symbol list) : int list =
  List.fold symbols ~init:empty_arities ~f:(fun acc sym ->
      Set.union acc (symbol_arities sym))
  |> Set.to_list
