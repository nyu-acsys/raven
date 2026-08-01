open Base
open Ast
open Util
open ExtApi

(** Implements `assert e with { proof }`, Raven's natural-deduction-style construct for
    proving a quantified (or plain) fact `e` via an auxiliary ghost proof block that is
    checked in isolation and then discarded, so its scratch work never pollutes the
    surrounding SMT state -- see docs/ext/README.md and CLAUDE.md for the general
    extension-API shape this follows.

    Soundness of the "prove once, discard the proof, keep only the conclusion" pattern
    below crucially depends on `e` being *pure* (no `own`/predicate/AU content): the
    surviving branch just `assume`s `e`, with nothing debiting whatever resource the
    proof consumed on its own (discarded) branch. This is enforced by type-checking `e`
    against `Type.bool` rather than the wider `Type.perm` ordinary assert/assume specs
    accept. When `e` is headed by `forall`, the bound variables are additionally forced
    `const` in the proof's scope, so the proof can't pin them to a specific witness and
    then illegitimately generalize; `exists`-headed goals leave them mutable, since the
    proof computing a concrete witness is exactly how existential introduction works
    and needs no such restriction. This is a core Raven construct, enabled by default
    (folded into `RavenCore` in lib/ext/ext.ml), not one more `--extension` choice. *)
module AssertWithExt (Cont : ListApi) = struct
  (* Every hook defaults to Cont's (including ListFns, since Cont : ListApi); only the
     ones actually overridden below need a definition. *)
  include Cont

  let lib_source = None

  type Stmt.stmt_ext +=
    | AssertWith of { spec : Stmt.spec; proof : Stmt.t }

  (* AstDef *)
  (* type_ext_to_name/expr_ext_to_string/pr_basic_stmt_ext/contract_ext_to_string/
     basic_stmt_ext_*: no type_ext/expr_ext/BasicStmtExt/contract_ext constructors
     here (this extension only adds a top-level StmtExt), so Cont's default is used. *)

  let pr_stmt_ext ppf stmt_ext =
    let open Stdlib.Format in
    match stmt_ext with
    | AssertWith { spec; _ } ->
        fprintf ppf "@[<2>[EXT]assert@ %a@ with@ { ... }@]" Expr.pr spec.spec_form
    | _ -> Cont.pr_stmt_ext ppf stmt_ext

  (* `AssertWith` is always lowered (by [rewrite_stmt_ext] below) long before any pass
     that consults these three -- same "empty by default" precedent already accepted
     for the [basic_stmt_ext_*] family (see astDef.ml's [default_basic_stmt_ext_symbols]
     and friends), and safer here besides: [proof] still carries raw [VarDef] nodes at
     this point, which [Stmt.stmt_local_vars_modified] et al. reject once lowering has
     normally already turned them into [Havoc]s. *)
  let stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | AssertWith _ -> Set.empty (module QualIdent)
    | _ -> Cont.stmt_ext_symbols stmt_ext

  let stmt_ext_local_vars_modified stmt_ext =
    match stmt_ext with
    | AssertWith _ -> []
    | _ -> Cont.stmt_ext_local_vars_modified stmt_ext

  let stmt_ext_fields_accessed stmt_ext =
    match stmt_ext with
    | AssertWith _ -> []
    | _ -> Cont.stmt_ext_fields_accessed stmt_ext

  let stmt_ext_is_recognized stmt_ext =
    match stmt_ext with
    | AssertWith _ -> true
    | _ -> Cont.stmt_ext_is_recognized stmt_ext

  (* Rewriter *)
  (* expr_ext_rewrite_types/basic_stmt_ext_rewrite_types: no expr_ext/BasicStmtExt
     constructors here, so Cont's default is used. *)

  let stmt_ext_rewrite ~(f : expr -> expr Rewriter.t) ~(c : Stmt.t -> Stmt.t Rewriter.t)
      (stmt_ext : Stmt.stmt_ext) : Stmt.stmt_ext Rewriter.t =
    let open Rewriter.Syntax in
    match stmt_ext with
    | AssertWith { spec; proof } ->
        let* spec_form = f spec.spec_form in
        let+ proof = c proof in
        AssertWith { spec = { spec with spec_form }; proof }
    | _ -> Cont.stmt_ext_rewrite ~f ~c stmt_ext

  (* Typing *)
  (* type_check_type_expr/type_check_expr/type_check_basic_stmt/
     type_check_contract_ext/check_contract_ext_group_compatible: no type_ext/expr_ext/
     BasicStmtExt/contract_ext constructors here, so Cont's default is used. *)

  let type_check_stmt_ext (call_decl : Callable.call_decl) (stmt_ext : Stmt.stmt_ext)
      (loc : location) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : type_check_stmt_functs) :
      (Stmt.stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t =
    let open Rewriter.Syntax in
    match stmt_ext with
    | AssertWith { spec; proof } ->
        (* Peel the syntactic (not yet type-checked) shape of the goal: a `forall`
           licenses generalizing from an arbitrary instance, so its bound variables
           must stay `const` throughout the proof; an `exists` is instead witnessed by
           the proof (typically via assignment), so its variables stay mutable; a bare,
           unquantified fact needs neither. *)
        let vs, var_const =
          match spec.spec_form with
          | Expr.Binder (Expr.Forall, vs, _, _, _) -> vs, true
          | Expr.Binder (Expr.Exists, vs, _, _, _) -> vs, false
          | _ -> [], true
        in
        let e1 =
          match spec.spec_form with
          | Expr.Binder ((Expr.Forall | Expr.Exists), _, _, e1, _) -> e1
          | e -> e
        in
        let vardefs =
          List.map vs ~f:(fun (decl : var_decl) ->
              let decl = { decl with Type.var_const } in
              Stmt.
                { stmt_desc =
                    Basic (VarDef { var_decl = decl; var_init = None; var_is_free = NotFree });
                  stmt_loc = decl.var_loc
                })
        in
        let assert_stmt = Stmt.mk_assert_expr ~loc:(Expr.to_loc e1) ~spec_error:spec.spec_error e1 in
        let assume_false = Stmt.mk_assume_expr ~loc (Expr.mk_bool ~loc false) in
        let checks_block =
          Stmt.mk_block_stmt ~loc ~ghost:true (vardefs @ [ proof; assert_stmt; assume_false ])
        in
        let nondet_var =
          Type.
            { var_name = Ident.fresh loc "$nondet";
              var_loc = loc;
              var_type = Type.bool |> Type.set_ghost true;
              var_const = true;
              var_ghost = true;
              var_implicit = false
            }
        in
        let nondet_var_def =
          Stmt.
            { stmt_desc = Basic (VarDef { var_decl = nondet_var; var_init = None; var_is_free = NotFree });
              stmt_loc = loc
            }
        in
        (* [spec]'s own [spec_form] is still the raw, not-yet-type-checked goal here --
           reused as-is for the `assume` below: type-checking the whole synthesized
           block in one pass (rather than type-checking [spec_form] separately, as a
           previous version of this code did) is what lets an ordinary [VarDef] like
           the ones above -- including this one -- go through the same VarDef-to-Havoc
           conversion, symbol registration, and ghost-scope propagation that
           [Typing.process_stmt] gives any other statement; splitting the checks across
           two separate calls left the synthesized `$nondet` local never actually
           registered as a symbol. *)
        let assume_spec_stmt = Stmt.mk_assume_spec ~loc spec in
        let cond_stmt =
          Stmt.
            { stmt_desc =
                Cond
                  { cond_test = Some (Expr.from_var_decl nondet_var);
                    cond_then = assume_spec_stmt;
                    cond_else = checks_block;
                    cond_if_assumes_false = false
                  };
              stmt_loc = loc
            }
        in
        let whole_block = Stmt.mk_block_stmt ~loc ~ghost:true [ nondet_var_def; cond_stmt ] in
        (* Type-checking [assume_spec_stmt]'s [spec.spec_form] here goes through the
           ordinary [Spec (Assume, _)] path, which checks it against [Type.perm] --
           the same wide expected type ordinary `assume`/`assert` accept. That's too
           permissive for what `with` claims to prove (see the module doc comment
           above): restrict it to [Type.bool] explicitly first, so an impure
           (`Perm`-typed, e.g. predicate) goal is rejected here rather than silently
           accepted and then unsoundly `assume`d for free below. *)
        let* _ =
          type_check_stmt_functs.disambiguate_process_expr spec.spec_form
            (Type.bool |> Type.set_ghost true) disam_tbl
        in
        let+ whole_block, disam_tbl =
          type_check_stmt_functs.process_stmt call_decl whole_block disam_tbl
        in
        (whole_block.stmt_desc, disam_tbl)
    | _ -> Cont.type_check_stmt_ext call_decl stmt_ext loc disam_tbl type_check_stmt_functs

  (* Rewrites *)
  (* rewrite_type_ext/rewrite_expr_ext/rewrite_basic_stmt_ext: no type_ext/expr_ext/
     BasicStmtExt constructors here, so Cont's default is used. *)

  (* [type_check_stmt_ext] above fully lowers [AssertWith] into ordinary statements
     (a [Cond] guarded by a fresh nondet local) itself, rather than leaving that to
     this hook -- see its comment on why the whole synthesized block has to be
     type-checked as one unit. An [AssertWith] therefore never reaches the rewrite
     phase; if it does, some caller built one directly instead of going through
     [type_check_stmt_ext], which is a bug. *)
  let rewrite_stmt_ext (stmt_ext : Stmt.stmt_ext) (loc : location) : Stmt.t Rewriter.t =
    match stmt_ext with
    | AssertWith _ ->
        Error.internal_error loc
          "AssertWith reached the rewrite phase unresolved (should have been fully \
           lowered by type_check_stmt_ext)"
    | _ -> Cont.rewrite_stmt_ext stmt_ext loc

  (* rewrite_contract_ext_call/rewrite_callable_entry/rewrite_contract_ext_loop_transfer:
     no contract_ext constructors here, so Cont's default is used. *)

  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
end
