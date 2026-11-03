open Base
open Ast
open ExtApi
open Util

(** Here, we implement an extension that adds support for Iris-style _prophecy variables_.
    This is what `--extension default` (equivalently, no `--extension` flag) activates --
    it has no flag of its own, and is mutually exclusive with the ErrorCredits extension
    (`--extension eris`), since combining the two is not sound.

    A prophecy variable denotes a value (or sequence of values) that will only be observed
    at a future point during program execution. In particular, the value may depend on
    non-deterministic choices (such as scheduler decisions) that will be made between the
    current point of execution and the point when the value will be observed. A prophecy
    variable allows one effectively to predict the outcome of such future choices and
    reason about them before they occur (e.g., via case analysis).

    The extension implements:
    - a parametric type `Proph[T]` whose values represent multi-shot prophecies p
      predicting an unbounded sequence of values of type T,
    - a parametric type `Proph[T, 1]` whose values represent one-shot prophecies p
      predicting a single value of type T, resolvable at most once,
    - a command `proph_id, proph_val := new Proph[T]` for creating new multi-shot
      prophecies,
    - a command `proph_id, proph_val := new Proph[T, 1]` for creating new one-shot
      prophecies,
    - `Proph.proph(proph_id, value)` for asserting/inhaling/exhaling the prophecy resource
      (value: List[T] for multi-shot, T for one-shot -- which shape is expected is
      determined by proph_id's own Proph[...] type),
    - a command `Proph.resolve(proph_id, value);` for resolving prophecies. *)

(* Parameterized over the plain `Ext` signature -- this extension builds/recognizes
   its `Library.List[T]` values directly (see `list_module_of` and friends below,
   and `ProgUtils.instantiate_type_functor`/`instantiation_arg`). *)
module ProphecyExt (Cont : Ext) = struct
  (* Every hook defaults to Cont's; only the ones actually overridden below need a
     definition. *)
  include Cont

  (* This extension's library, which programs cannot name. *)
  let lib_source =
    Some
      ( ExtApi.Elaboration_unit,
        ("lib/ext/prophecyExt/prophecyLib.rav", [%blob "prophecyLib.rav"]) )

  (* Defining pre-fixed idents from the `Prophecy` module defined in prophecyLib.rav. This module is part of the unit [Predefs.elaboration_ident], which programs cannot name. We instantiate this module once for each type T used in the program -- both prophecy flavors for a given T share that single instantiation, each backed by its own field on its own bare type parameter (see the module-level doc comment in prophecyLib.rav for why it's shaped this way, and `field_ident` below). *)
  module ProphPredefs = struct
    let proph_mod_ident = Ident.make Loc.dummy "Prophecy" 0
    let proph_mod_qi = QualIdent.from_list [ Predefs.elaboration_ident; proph_mod_ident ]

    let field_ident one_shot =
      if one_shot then Ident.make Loc.dummy "prophecyValue1" 0
      else Ident.make Loc.dummy "prophecyValue" 0

    (* Custom prefix used for generating Prophecy module names. Using `$` in Raven
       makes the ident safe from collisions with user-defined modules, because `$`
       is not supported by Raven's parser. *)
    let proph_mod_ident_prefix = "ProphecyMod$"
  end

  (* Type for Prophecy variables, parametric in the predicted element type. The bool
     records whether this is a one-shot ([true]) or multi-shot ([false]) prophecy --
     `Proph[T, 1]` vs `Proph[T]` at the surface level. *)
  type Type.type_ext += ProphId of bool

  (* Checked forms carry their resolved ghost field as a third internal operand.
     Multi-shot resolution also carries a typed length application naming its list
     module. Source forms accept exactly two operands. *)
  type Expr.expr_ext +=
    | ProphResource of bool * type_expr
    | CheckedProphResource of bool * type_expr

  type Stmt.stmt_ext +=
    | NewProph of bool * type_expr
    | ResolveProph of bool * type_expr
    | CheckedNewProph of bool * type_expr
    | CheckedResolveProph of bool * type_expr

  (* This is what type_expr in Raven look like.
      The arguments to Type.mk_app in order:
      - ~loc: location information in source code used for error printing
      - ~ghost: indicates whether the type is a _ghost_ type, ie only part of proof, not the executable program.
      - (TypeExt (ProphId one_shot)): This is a type construct `Type.constr`, used to annotate types. Specifically, `TypeExt` denotes an "extension" type.
      - [typ]: The single type argument -- the type of the values this prophecy predicts.
  *)
  let proph_id_type ~loc ~one_shot typ =
    Type.mk_app ~loc ~ghost:true (TypeExt (ProphId one_shot)) [ typ ]

  let source_expr = function
    | CheckedProphResource (one_shot, typ) -> ProphResource (one_shot, typ)
    | ext -> ext

  let source_stmt = function
    | CheckedNewProph (one_shot, typ) -> NewProph (one_shot, typ)
    | CheckedResolveProph (one_shot, typ) -> ResolveProph (one_shot, typ)
    | ext -> ext

  let source_arguments = function
    | first :: second :: _metadata -> [ first; second ]
    | arguments -> arguments

  (** AstDef *)

  (* Standard pattern: match on our constructors, defer the rest. *)
  let type_ext_to_name type_ext =
    match type_ext with ProphId _ -> "Proph" | _ -> Cont.type_ext_to_name type_ext

  let expr_ext_to_string expr_ext =
    match source_expr expr_ext with
    | ProphResource _ -> "Proph.proph"
    | _ -> Cont.expr_ext_to_string expr_ext

  let pr_expr_ext ~names ~pr ppf expr_ext args =
    match (source_expr expr_ext, source_arguments args) with
    | ProphResource _, [ proph_id; proph_val ] ->
        Stdlib.Format.fprintf ppf "Proph.proph(%a, %a)" pr proph_id pr proph_val
    | _ -> Cont.pr_expr_ext ~names ~pr ppf expr_ext args

  (* Standard format for printer functions. *)
  let pr_basic_stmt_ext (printers : Stmt.ext_printers) ppf ext expr_list =
    let open Stdlib.Format in
    match (source_stmt ext, source_arguments expr_list) with
    | NewProph (b, typ), [ proph_id; proph_val ] ->
        fprintf ppf "@[%a, %a@ :=@ new Proph[%a%s]@]" printers.pr_expr proph_id
          printers.pr_expr proph_val printers.pr_type typ
          (if b then ", 1" else "")
    (* Make sure to have a case for malformed arguments; ensures we catch all our cases. *)
    | NewProph _, _ ->
        Error.internal_error Loc.dummy "wrong number of arguments for new Proph(...)"
    | ResolveProph _, [ proph_id; resolve_val ] ->
        fprintf ppf "@[Proph.resolve(%a, %a)@]" printers.pr_expr proph_id printers.pr_expr
          resolve_val
    | ResolveProph _, _ ->
        Error.internal_error Loc.dummy "wrong number of arguments for Proph.resolve(...)"
    | _ -> Cont.pr_basic_stmt_ext printers ppf ext expr_list

  (* This is almost always expected to be empty. Only to be used if one stores variables/names within the Stmt _constructor_. Typically all the additional arguments are stored as stmt_args *)
  let basic_stmt_ext_symbols stmt_ext =
    match source_stmt stmt_ext with
    | NewProph _ -> Set.empty (module QualIdent)
    | ResolveProph _ -> Set.empty (module QualIdent)
    | _ -> Cont.basic_stmt_ext_symbols stmt_ext

  (* This one is more nuanced. Given the statement extension and all its expression arguments (ie the entire statement), we are supposed to return a list of local variables that are modified.

  This is used internally during the SSA transformation to determine whether to redefine a local var.
  *)
  let basic_stmt_ext_local_vars_modified stmt_ext exprs =
    match (source_stmt stmt_ext, source_arguments exprs) with
    | NewProph _, [ proph_id; proph_val ] ->
        if Expr.is_ident proph_val then
          (* We only return `proph_val` if it is an `ident`, or a local variable (as opposed to a `qual_ident` if it were a global `val`) *)
          [ Expr.to_ident proph_id; Expr.to_ident proph_val ]
        else
          (* Must be a bit careful with `Expr.to_ident`. This method crashes if underlying expression is not an ident *)
          [ Expr.to_ident proph_id ]
    (* Catching general arguments *)
    | NewProph _, _ ->
        Error.internal_error Loc.dummy "wrong number of arguments for new Proph(...)"
    | ResolveProph _, [ proph_id; resolve_val ] ->
        (* In this case, no _variables_ are being updated, only resources are manipulated.  *)
        []
    | ResolveProph _, _ ->
        Error.internal_error Loc.dummy "wrong number of arguments for Proph.resolve(...)"
    | _ -> Cont.basic_stmt_ext_local_vars_modified stmt_ext exprs

  (* Utility function to generate canonical module name. Using `Type.to_string` to convert the underlying type to a string. Using `ProgUtils.serialize` to make sure the name is compatible with SMT. Using `Ident.make` instead of `Ident.fresh` because we want all references to this ident to be to the same module. One instantiation per T serves both prophecy flavors (see `ProphPredefs.field_ident`), so there is no shot-kind parameter here.  *)
  let prophecy_module_ident ~loc typ =
    let prophecy_mod_string = ProphPredefs.proph_mod_ident_prefix ^ Type.to_string typ in
    Ident.make loc (ProgUtils.serialize prophecy_mod_string) 0

  (* A multi-shot prophecy's value is a sequence of predicted values, `Library.List[T]`
     -- an ordinary generic-module instantiation like any other, built directly via
     `ProgUtils.instantiate_type_functor`, the functor-agnostic primitive behind any
     instantiation of a generic module. *)
  let list_module_of ~loc (elem_typ : type_expr) : QualIdent.t Rewriter.t =
    let open Rewriter.Syntax in
    let* lib_list_module =
      Rewriter.find_and_reify_module Predefs.lib_list_mod_qual_ident
    in
    ProgUtils.instantiate_type_functor ~loc ~f:!Rewriter.check_symbol_ref
      ~functor_qual_ident:Predefs.lib_list_mod_qual_ident
      ~functor_mod_decl:lib_list_module.mod_decl [ elem_typ ]

  let list_type_of ~loc (elem_typ : type_expr) : type_expr Rewriter.t =
    let open Rewriter.Syntax in
    let+ list_module_qi = list_module_of ~loc elem_typ in
    Type.mk_var ~loc (QualIdent.append list_module_qi Predefs.lib_type_rep_type_ident)

  (* `hd`/`tl`/`len` of a `list_module_qi`-instantiated list value, built directly as
     ordinary DataDestr/Var-headed applications against that instantiation's own
     members, since this extension already knows exactly which instantiation is
     meant at the point it builds these -- no extension-tag-then-rewrite round trip
     needed. *)
  let list_hd ~loc ~elem_typ list_module_qi ls_expr =
    Expr.mk_app ~loc ~typ:elem_typ
      (DataDestr (QualIdent.append list_module_qi Predefs.lib_list_head_destr_ident))
      [ ls_expr ]

  let list_tl ~loc ~list_typ list_module_qi ls_expr =
    Expr.mk_app ~loc ~typ:list_typ
      (DataDestr (QualIdent.append list_module_qi Predefs.lib_list_tail_destr_ident))
      [ ls_expr ]

  let list_len ~loc list_module_qi ls_expr =
    Expr.mk_app ~loc ~typ:Type.int
      (Var (QualIdent.append list_module_qi Predefs.lib_list_len_ident))
      [ ls_expr ]

  (* Checked operands retain the field selected before representation lowering. *)
  let basic_stmt_ext_fields_accessed stmt_ext exprs =
    match (stmt_ext, exprs) with
    | (CheckedNewProph _ | CheckedResolveProph _), _ :: _ :: field :: _metadata ->
        [ Expr.to_qual_ident field ]
    | (NewProph _ | ResolveProph _), _ -> []
    | _ -> Cont.basic_stmt_ext_fields_accessed stmt_ext exprs

  (* pr_stmt_ext/stmt_ext_*: no top-level StmtExt constructors here, so Cont's default
     is used. *)

  let type_ext_is_recognized type_ext =
    match type_ext with ProphId _ -> true | _ -> Cont.type_ext_is_recognized type_ext

  let expr_ext_is_recognized expr_ext =
    match source_expr expr_ext with
    | ProphResource _ -> true
    | _ -> Cont.expr_ext_is_recognized expr_ext

  let stmt_ext_is_recognized stmt_ext =
    match source_stmt stmt_ext with
    | NewProph _ | ResolveProph _ -> true
    | _ -> Cont.stmt_ext_is_recognized stmt_ext

  (* Both lower to ghost blocks over the ghost prophecy field: a resolution has to
     sit alongside the physical step it is attached to (Iris's `Resolve e p v`),
     so charging it a step of its own would make exactly that pattern impossible. *)
  let stmt_ext_atomicity stmt_ext =
    match source_stmt stmt_ext with
    | NewProph _ | ResolveProph _ -> Stmt.NoStep
    | _ -> Cont.stmt_ext_atomicity stmt_ext

  (* contract_ext_is_recognized: no contract_ext constructors here, so Cont's default
     is used. *)

  (* Rewriter *)

  (* Preserve surface element annotations for printing and rechecking. Resolved
     fields are ordinary expression operands, so substitution and lowering traverse
     their identifiers and types without reconstructing a prophecy instance. *)
  let expr_ext_rewrite_types ~f expr_ext =
    match source_expr expr_ext with
    | ProphResource _ -> Rewriter.return expr_ext
    | _ -> Cont.expr_ext_rewrite_types ~f expr_ext

  let basic_stmt_ext_rewrite_types ~f stmt_ext =
    match source_stmt stmt_ext with
    | NewProph _ | ResolveProph _ -> Rewriter.return stmt_ext
    | _ -> Cont.basic_stmt_ext_rewrite_types ~f stmt_ext

  (* stmt_ext_rewrite: no top-level StmtExt constructor here, so Cont's default is
     used. *)

  (* Typing *)

  (* Perform type-checking on type_expr. The underlying type is stored in the AST as follows:
    Type.App (TypeExt type_ext, type_args, type_attr)

    type_check_type_expr_functs contains functions of the type checker useful for type-checking. These are defined in ExtApi.ml.
  *)
  let type_check_type_expr type_ext type_args type_attr type_check_type_expr_functs =
    let open Rewriter.Syntax in
    match (type_ext, type_args) with
    | ProphId one_shot, [ t ] ->
        (* Recursively type-check the element type argument, same as List[T]. Making sure to set Type.ghost. *)
        let+ t = type_check_type_expr_functs.check_type_expr t in
        Type.App (TypeExt (ProphId one_shot), [ t ], type_attr) |> Type.set_ghost true
    | ProphId _, _ ->
        (* Raise type_error otherwise. *)
        Error.type_error type_attr.Type.type_loc
          "Proph[...] type expects exactly one type argument (the element type)"
    | _ ->
        Cont.type_check_type_expr type_ext type_args type_attr type_check_type_expr_functs

  let initialize_prophecy_module loc (typ : type_expr) : qual_ident Rewriter.t =
    let open Rewriter.Syntax in
    let* proph_module_insert_scope, proph_module_reference_scope =
      ProgUtils.find_insertion_scope_for_types [ typ ]
    in
    let proph_module_qi =
      QualIdent.append proph_module_reference_scope (prophecy_module_ident ~loc typ)
    in

    Logs.debug (fun m ->
        m "[EXT] ProphecyExt.initialize_prophecy_module: Looking up proph_module_qi: %a"
          QualIdent.pr proph_module_qi);
    let* lookup = Rewriter.resolve_and_find_opt proph_module_qi in

    match lookup with
    | Some _ ->
        (* Found an existing module there. Simply return the qual_ident. *)
        Logs.debug (fun m ->
            m
              "[EXT] ProphecyExt.initialize_prophecy_module: Look-up succeeded for \
               proph_module_qi: %a"
              QualIdent.pr proph_module_qi);
        Rewriter.return proph_module_qi
    | None ->
        Logs.debug (fun m ->
            m
              "[EXT] ProphecyExt.initialize_prophecy_module: Proph module not found. \
               Initializing... proph_module_qi: %a"
              QualIdent.pr proph_module_qi);

        (* Proph module not found. Initializing... *)
        let type_module_for rep_typ =
          ProgUtils.get_or_intros_rep_module ~loc ~f:!Rewriter.check_symbol_ref
            ~insert_scope:proph_module_insert_scope
            ~reference_scope:proph_module_reference_scope
            ~interface_qual_ident:Predefs.lib_type_mod_qual_ident
            ~rep_ident:Predefs.lib_type_rep_type_ident rep_typ
        in

        let* multi_value_typ = list_type_of ~loc typ in
        let* multi_type_module_qi = type_module_for multi_value_typ in
        let* one_type_module_qi = type_module_for typ in

        (* Finally, we generate the name for the final Prophecy module. *)
        let proph_module_ident = prophecy_module_ident ~loc typ in

        (* Definition of module instantiation. This is equivalent to the Raven syntax:
        ```
          proph_module_ident = ProphPredefs.proph_mod_qi [ multi_type_module_qi, one_type_module_qi ]
        ```
       *)
        let proph_module_inst =
          Module.ModInst
            (Module.mk_mod_inst ~name:proph_module_ident ~typ:ProphPredefs.proph_mod_qi
               ~def:
                 ( ProphPredefs.proph_mod_qi,
                   [
                     Module.ModArg multi_type_module_qi; Module.ModArg one_type_module_qi;
                   ] )
               ~loc ())
        in

        Logs.debug (fun m ->
            m
              "[EXT] ProphecyExt.initialize_prophecy_module: proph_module_ident = %a; \
               about to introduce"
              Ident.pr proph_module_ident);

        (* Finally, we call the `Rewriter.introduce_typecheck_symbol_at_scope'` to type-check this symbol, and finally introduce the type-checked symbol to the AST. If the type-check fails, the program crashes, so be careful! *)
        let* _proph_module_inst_qi =
          Rewriter.introduce_typecheck_symbol_at_scope' ~loc proph_module_inst
            proph_module_insert_scope
        in

        Rewriter.return proph_module_qi

  let prophecy_field ~loc ~one_shot typ =
    let open Rewriter.Syntax in
    let* module_qi = initialize_prophecy_module loc typ in
    let field_qi = QualIdent.append module_qi (ProphPredefs.field_ident one_shot) in
    let+ field = Rewriter.find_and_reify_field field_qi in
    Expr.mk_var ~typ:field.field_type (QualIdent.set_loc loc field_qi)

  (* Type-checking of expressions. The underlying expression in the AST that we are type-checking is:
      Expr.App ((ExprExt expr_ext), expr_list, expr_attr)

    expected_typ contains typing hints from the surrounding env, but is often `Type.any`.
  *)
  let rec type_check_expr (expr_ext : Expr.expr_ext) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) (expected_typ : type_expr)
      (type_check_expr_functs : type_check_expr_functs) =
    let open Rewriter.Syntax in
    let loc = expr_attr.expr_loc in

    match (expr_ext, expr_list) with
    | CheckedProphResource (one_shot, typ), [ id; value; _field ] ->
        type_check_expr
          (ProphResource (one_shot, typ))
          [ id; value ] expr_attr expected_typ type_check_expr_functs
    (* These are the arguments we expect. *)
    | ProphResource _, [ proph_id_expr; value_expr ] ->
        (* Type-checking proph_id_expr against `Type.any`: its declared type (some
         `Proph[T]`/`Proph[T, 1]`) tells us both the element type T and whether the
         second argument should be a `T` (one-shot) or a `List[T]` (multi-shot). *)
        let* proph_id_expr =
          type_check_expr_functs.check_expr proph_id_expr (Type.any |> Type.set_ghost true)
        in

        let one_shot, elem_typ =
          match Expr.to_type proph_id_expr with
          | Type.App (TypeExt (ProphId one_shot), [ t ], _) -> (one_shot, t)
          | tp ->
              Error.type_error loc
                ("Proph.proph(...) expects its first argument to be a Proph[...] value; \
                  found: " ^ Type.to_string_user tp)
        in

        let* expected_value_typ =
          if one_shot then Rewriter.return (elem_typ |> Type.set_ghost true)
          else
            let+ list_typ = list_type_of ~loc elem_typ in
            list_typ |> Type.set_ghost true
        in

        (* Type-checking value_expr *)
        let* value_expr =
          type_check_expr_functs.check_expr value_expr expected_value_typ
        in

        let+ field = prophecy_field ~loc ~one_shot elem_typ in
        Expr.mk_app ~loc ~typ:Type.perm
          (ExprExt (CheckedProphResource (one_shot, elem_typ)))
          [ proph_id_expr; value_expr; field ]
    (* Incorrect number of arguments found; raise a type_error. *)
    | ProphResource _, _ ->
        Error.type_error loc "Proph.proph(...) called with incorrect number of arguments"
    | _ ->
        Cont.type_check_expr expr_ext expr_list expr_attr expected_typ
          type_check_expr_functs

  (* Type-checking of stmts. The underlying stmt in the AST is represented as:
      Stmt.{
        stmt_desc = Basic (BasicStmtExt (stmt_ext, expr_list));
        stmt_loc = stmt_loc;
      }

    `disam_tbl` is a data structure used to disambiguate local variables occuring in different subscopes by assigning a unique `ident_num` to each local variable. There is no need to understand how this works or to manipulate this manually. Some functions require and return this argument, which indicates how this must be used. However, care must be made to update and return this correctly.

    This function returns a `Stmt.basic_stmt_desc`. This is an object like:
      (BasicStmtExt (stmt_ext, expr_list))
    In addition, a `disam_tbl` must be returned.
    `type_check_stmt_functs` is again a set of functions of the type checker that are useful for type-checking statements.
  *)
  (* type_check_contract_ext/check_contract_ext_group_compatible/
     contract_ext_to_string: no contract_ext constructors here, so Cont's default is
     used. *)

  let rec type_check_basic_stmt call_decl (stmt_ext : Stmt.stmt_ext)
      (expr_list : expr list) (stmt_loc : Loc.t)
      (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : ExtApi.type_check_stmt_functs) :
      (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t =
    (* A Raven debug statement. *)
    Logs.debug (fun m -> m "[EXT] ProphecyExt.type_check_basic_stmt: started");

    let open Rewriter.Syntax in
    (* Determining whether we are in a ghost scope. Certain actions aren't allowed in ghost scopes, such as making concrete program steps, procedure calls, etc. *)
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    match (stmt_ext, expr_list) with
    | CheckedNewProph _, [ id; value; _field ] ->
        let one_shot, typ =
          match Expr.to_type id with
          | Type.App (TypeExt (ProphId one_shot), [ typ ], _) -> (one_shot, typ)
          | _ ->
              Error.internal_error stmt_loc
                "A checked prophecy allocation has no prophecy type"
        in
        type_check_basic_stmt call_decl
          (NewProph (one_shot, typ))
          [ id; value ] stmt_loc disam_tbl type_check_stmt_functs
    | CheckedResolveProph _, id :: value :: _metadata ->
        type_check_basic_stmt call_decl (source_stmt stmt_ext) [ id; value ] stmt_loc
          disam_tbl type_check_stmt_functs
    (* ```proph_id, proph_val := new Proph[typ]``` / ```new Proph[typ, 1]``` *)
    | NewProph (oneshot_b, typ), [ proph_id; proph_val ] ->
        (* Type-check `proph_id` against the Proph[typ]/Proph[typ, 1] type -- this both
         checks/binds `proph_id` and, if it was already declared with a different
         Proph[...] type, catches the mismatch here. From `type_check_basic_stmt`, we must call `disambiguate_and_check_expr, instead of `check_expr` to make sure we use `disam_tbl` consistently.  *)
        let* proph_id =
          type_check_stmt_functs.disambiguate_and_check_expr proph_id
            (proph_id_type ~loc:stmt_loc ~one_shot:oneshot_b typ)
            disam_tbl
        in

        let typ =
          match Expr.to_type proph_id with
          | Type.App (TypeExt (ProphId _), [ typ ], _) -> typ
          | _ ->
              Error.internal_error stmt_loc
                "A checked prophecy allocation must have a prophecy type"
        in
        let* proph_val_typ =
          if oneshot_b then
            (* If it is a one-shot prophecy, the type for `proph_val` is same as the type annotation on `new Proph[..., 1]`, ie `typ` *)
            Rewriter.return (typ |> Type.set_ghost true)
          else
            (* Else, the type for `proph_val` is `Library.List[typ].T`. *)
            let+ list_typ = list_type_of ~loc:stmt_loc typ in
            list_typ |> Type.set_ghost true
        in

        begin match Expr.is_ident proph_val with
        | false ->
            (* Must be called on a local variable; otherwise type_error. *)
            Error.type_error stmt_loc
              "new Proph(...) must be assigned to a local variable"
        | true ->
            (* Type-checking proph_val. *)
            let* proph_val =
              type_check_stmt_functs.disambiguate_and_check_expr proph_val proph_val_typ
                disam_tbl
            in

            (* Everything checks out. Constructing final `Stmt.basic_stmt_desc` to return.
          Making sure to use updated and type-checked values `proph_id` and `proph_val`. not stale values.
        *)
            let+ field = prophecy_field ~loc:stmt_loc ~one_shot:oneshot_b typ in
            ( Stmt.BasicStmtExt
                (CheckedNewProph (oneshot_b, typ), [ proph_id; proph_val; field ]),
              disam_tbl )
        end
    | NewProph _, _ ->
        Error.type_error stmt_loc
          "new Proph(...) called with incorrect number of arguments"
        (* ```Proph.resolve(proph_id, resolve_value)``` *)
    | ResolveProph _, [ proph_id; resolve_value ] ->
        (* Type-checking proph_id against `Type.any`: its declared Proph[...] type tells
         us the predicted element type T and whether this is a one-shot or multi-shot
         prophecy. *)
        let* proph_id =
          type_check_stmt_functs.disambiguate_and_check_expr proph_id
            (Type.any |> Type.set_ghost true)
            disam_tbl
        in

        let one_shot, elem_typ =
          match Expr.to_type proph_id with
          | Type.App (TypeExt (ProphId one_shot), [ t ], _) -> (one_shot, t)
          | tp ->
              Error.type_error stmt_loc
                ("Proph.resolve(...) expects its first argument to be a Proph[...] \
                  value; found: " ^ Type.to_string_user tp)
        in

        let* resolve_value =
          type_check_stmt_functs.disambiguate_and_check_expr resolve_value
            (elem_typ |> Type.set_ghost true)
            disam_tbl
        in

        (* Constructing final return `Stmt.basic_stmt_desc` *)
        let* field = prophecy_field ~loc:stmt_loc ~one_shot elem_typ in
        let+ list_metadata =
          if one_shot then Rewriter.return []
          else
            let+ list_module_qi = list_module_of ~loc:stmt_loc elem_typ in
            let empty =
              Expr.mk_app ~loc:stmt_loc
                ~typ:(Type.field_val (Expr.to_type field))
                (DataConstr
                   (QualIdent.append list_module_qi (Ident.make stmt_loc "nil" 0)))
                []
            in
            [ list_len ~loc:stmt_loc list_module_qi empty ]
        in
        ( Stmt.BasicStmtExt
            ( CheckedResolveProph (one_shot, elem_typ),
              [ proph_id; resolve_value; field ] @ list_metadata ),
          disam_tbl )
    | ResolveProph _, _ ->
        Error.type_error stmt_loc
          "Proph.resolve(...) called with incorrect number of arguments"
    | _ ->
        Cont.type_check_basic_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl
          type_check_stmt_functs

  (* type_check_stmt_ext: no top-level StmtExt constructor here, so Cont's default is
     used. *)

  (* Rewrites *)

  (* Now, we finally come to rewriting.

    We replace any reference to `Proph[T]` type with references (`Ref`s). This is because prophecies are modeled using resources, and in Raven only `Ref`s can have resources associated (one per field). The type argument (and shot-kind) only matter for picking which field to associate; the erased runtime representation is the same `Ref` either way.

    *)

  let rewrite_type_ext (type_ext : Type.type_ext) (tp_list : type_expr list)
      (loc : location) : type_expr Rewriter.t =
    match (type_ext, tp_list) with
    | ProphId _, [ _ ] -> Rewriter.return Type.ref
    | ProphId _, _ ->
        Error.type_error loc
          "Proph[...] type expects exactly one type argument (the element type)"
    | _ -> Cont.rewrite_type_ext type_ext tp_list loc

  (* Rewriting expressions. *)
  let rewrite_expr_ext (expr_ext : Expr.expr_ext) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) =
    let loc = expr_attr.expr_loc in
    match (expr_ext, expr_list) with
    | CheckedProphResource _, [ proph_id; value; field ] ->
        (* Finally, replace the `ProphResource` with its equivalent separation-logic resource, constructed with the `Own` constructor.

      Arguments to the Own constructor are:
      - The expression for the Ref.
      - An expression for the field.
      - A value expression.
      - A real number to denote fractional ownership. Here we use 1.0 to denote total ownership.

      *)
        Expr.mk_app ~typ:Type.perm ~loc Own
          [ proph_id; field; value; Expr.mk_real ~loc 1.0 ]
        |> Rewriter.return
    | _ -> Cont.rewrite_expr_ext expr_ext expr_list expr_attr

  (* contract_ext_rewrite_exprs/rewrite_contract_ext_call/rewrite_callable_entry/
     rewrite_contract_ext_loop_transfer: no contract_ext constructors here, so Cont's
     default is used. *)

  (* Rewriting Statements *)
  let rewrite_basic_stmt_ext (stmt_ext : Stmt.stmt_ext) (expr_list : expr list) loc :
      Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    Logs.debug (fun m -> m "[EXT] ProphecyExt.rewrite_stmt: Starting");

    match (stmt_ext, expr_list) with
    (* ```proph_id, proph_val := new Proph[typ]``` / ```new Proph[typ, 1]``` *)
    | CheckedNewProph _, [ proph_id; proph_val; field ] ->
        (* Building Raven statements to encode semantics. *)
        (* ```havoc proph_id``` *)
        let havoc_stmt1 = Stmt.mk_havoc ~loc (Expr.to_qual_ident proph_id) in
        (* ```havoc proph_val``` *)
        let havoc_stmt2 = Stmt.mk_havoc ~loc (Expr.to_qual_ident proph_val) in

        (* `proph_val` is already of the field's shape either way: `List[typ]` for a
         multi-shot prophecy, plain `typ` for a one-shot one -- see the `proph_val_typ`
         computed during type-checking. So, unlike before genericity, there is no need
         to fabricate an arbitrary tail here for the one-shot case: its field is not a
         list at all. *)
        let proph_new_stmt =
          Stmt.mk_inhale_expr ~loc ~cmnt:"[EXT] ProphExt: Inhale stmt for new Proph()"
            (Expr.mk_app ~loc ~typ:Type.perm Expr.Own
               [ proph_id; field; proph_val; Expr.mk_real 1.0 ])
        in

        (* Create a block_stmt containing all the statements. This block is indeed a ghost block, so setting ~ghost:true *)
        Rewriter.return
          (Stmt.mk_block_stmt ~loc ~kind:Stmt.Ghost
             [ havoc_stmt1; havoc_stmt2; proph_new_stmt ])
    | NewProph _, _ ->
        Error.internal_error loc
          "unexpected argument count for new Proph(...) at rewrite time (already \
           validated during type-checking)"
    (* For ```Proph.resolve(proph_id, resolve_value)``` statements *)
    | ( CheckedResolveProph (one_shot, _),
        proph_id :: resolve_value :: field :: list_metadata ) ->
        let prophecy_field_qi = QualIdent.set_loc loc (Expr.to_qual_ident field) in
        let proph_read_tp = Type.field_val (Expr.to_type field) in
        let typ = Expr.to_type resolve_value in
        let list_module_qi =
          match (one_shot, list_metadata) with
          | true, [] -> None
          | false, [ length ] -> Some (QualIdent.pop (Expr.to_qual_ident length))
          | _ -> Error.internal_error loc "A checked prophecy has invalid list metadata"
        in

        (* Creating new local variable to store value of `proph_id.prophecy_field` *)
        let proph_read_var_def, proph_read_var_ident =
          (* Ident.fresh to generate new fresh ident. *)
          let proph_read_var_ident = Ident.fresh loc "$proph_read" in

          (* Creating a `var_def` object, used to introduce the new local variable. *)
          ( Stmt.
              {
                var_decl =
                  Type.mk_var_decl ~ghost:true proph_read_var_ident ~loc proph_read_tp;
                var_init = None;
                var_is_free = NotFree;
              },
            proph_read_var_ident )
        in

        let* proph_id_var_def =
          Rewriter.find_and_reify_var (Expr.to_qual_ident proph_id)
        in

        let* _ = Rewriter.introduce_symbol (VarDef proph_read_var_def) in

        (* Constructing field_read stmt, by hand. Equivalent to:
        ```proph_read_var := proph_id.prophecy_field_qi;```
      *)
        let field_read_stmt =
          let field_read_desc =
            Stmt.
              {
                field_read_lhs = QualIdent.from_ident proph_read_var_ident;
                field_read_field = prophecy_field_qi;
                field_read_ref =
                  Expr.set_loc (Expr.from_var_decl proph_id_var_def.var_decl) loc;
                field_read_is_init = true;
              }
          in

          Stmt.{ stmt_desc = Basic (FieldRead field_read_desc); stmt_loc = loc }
        in

        if one_shot then
          (* One-shot: assert the resolved value matches the predicted one, then
           *exhale* the resource -- with no matching re-inhale, ownership of it is
           spent for good, so a second `Proph.resolve` on the same `proph_id` has no
           permission left to read the field. That is what makes a one-shot
           prophecy actually resolvable at most once, rather than merely by
           convention. *)
          (* Checked explicitly, with a message specific to this extension, so that a
           missing resource here doesn't surface `field_read_stmt`'s own generic
           "Could not assert sufficient permissions to access this field" -- which
           would leak the fact that prophecies are encoded as a hidden field on a
           `Ref` under the hood. The message only states what's actually missing --
           the resource isn't available *at this point in the proof* -- not why: it
           may genuinely already have been spent by an earlier `Proph.resolve`, but
           it could just as well still be held, only somewhere this proof hasn't
           gotten it from yet (an unopened invariant, say). Existentially quantified
           over the field's value: we don't know it yet (that's what
           `field_read_stmt` is about to find out), only that we still hold the
           resource at all. If this holds, `field_read_stmt`'s own check trivially
           holds too, so this is the only message a user ever sees. *)
          let has_resource_check_stmt =
            let v_var_decl =
              Type.mk_var_decl ~ghost:true (Ident.fresh loc "v") ~loc proph_read_tp
            in
            let has_resource_expr =
              Expr.mk_binder ~loc ~typ:Type.bool Exists [ v_var_decl ]
                (Expr.mk_app ~loc ~typ:Type.perm Expr.Own
                   [
                     Expr.from_var_decl proph_id_var_def.var_decl;
                     field;
                     Expr.from_var_decl v_var_decl;
                     Expr.mk_real ~loc 1.0;
                   ])
            in
            let error =
              ( Error.Verification
                  (Error.Extension { extension = "prophecy"; name = "resource" }),
                loc,
                "This prophecy's resource is not available here -- it may already have \
                 been resolved, or it may still be held elsewhere in the proof" )
            in
            Stmt.mk_assert_expr ~loc
              ~cmnt:
                "[EXT] ProphecyExt: check the one-shot prophecy's resource is available \
                 to resolve"
              ~spec_error:[ Stmt.mk_const_spec_error error ]
              has_resource_expr
          in

          let prophetic_assertion =
            Stmt.mk_assume_expr ~loc ~cmnt:"[EXT] ProphecyExt: Prophecising Assertion"
              (Expr.mk_eq resolve_value (Expr.from_var_decl proph_read_var_def.var_decl))
          in

          let exhale_stmt =
            Stmt.mk_exhale_expr ~loc
              ~cmnt:
                "[EXT] ProphecyExt: one-shot prophecy resource is fully consumed by \
                 resolve"
              (Expr.mk_app ~loc ~typ:Type.perm Expr.Own
                 [
                   Expr.from_var_decl proph_id_var_def.var_decl;
                   field;
                   Expr.from_var_decl proph_read_var_def.var_decl;
                   Expr.mk_real ~loc 1.0;
                 ])
          in

          Rewriter.return
            (Stmt.mk_block_stmt ~loc ~kind:Stmt.Ghost
               [
                 has_resource_check_stmt;
                 field_read_stmt;
                 prophetic_assertion;
                 exhale_stmt;
               ])
        else
          let list_module_qi =
            match list_module_qi with
            | Some qi -> qi
            | None ->
                Error.internal_error loc
                  "A checked multi-shot prophecy has no list module"
          in

          (* Add assumption about the prophecy, as an `assume` stmt.
        ```assume resolve_value = proph_read_var.hd```
      *)
          let prophetic_assertion =
            Stmt.mk_assume_expr ~loc ~cmnt:"[EXT] ProphecyExt: Prophecising Assertion"
              (Expr.mk_eq resolve_value
                 (list_hd ~loc ~elem_typ:typ list_module_qi
                    (Expr.from_var_decl proph_read_var_def.var_decl)))
          in

          (* ```assume len(proph_read_var) > 2``` *)
          let list_non_empty =
            Stmt.mk_assume_expr ~loc
              ~cmnt:"[EXT] ProphecyExt: Assuming remaining prophecy stream non-empty"
              (Expr.mk_app ~loc ~typ:Type.bool Gt
                 [
                   list_len ~loc list_module_qi
                     (Expr.from_var_decl proph_read_var_def.var_decl);
                   Expr.mk_int 2;
                 ])
          in

          (* ```proph_read_var.tl``` *)
          let field_write_val =
            list_tl ~loc ~list_typ:proph_read_tp list_module_qi
              (Expr.from_var_decl proph_read_var_def.var_decl)
          in

          (* ```proph_id.prophecy_field_qi := field_write_val;``` *)
          let field_write_stmt =
            let field_write_desc =
              Stmt.
                {
                  field_write_ref = Expr.from_var_decl proph_id_var_def.var_decl;
                  field_write_field = prophecy_field_qi;
                  field_write_val;
                }
            in

            Stmt.{ stmt_desc = Basic (FieldWrite field_write_desc); stmt_loc = loc }
          in

          Rewriter.return
            (Stmt.mk_block_stmt ~loc ~kind:Stmt.Ghost
               [ field_read_stmt; prophetic_assertion; list_non_empty; field_write_stmt ])
    | ResolveProph _, _ ->
        Error.internal_error loc
          "unexpected argument count for Proph.resolve(...) at rewrite time (already \
           validated during type-checking)"
    | _ -> Cont.rewrite_basic_stmt_ext stmt_ext expr_list loc

  (* rewrite_stmt_ext: no top-level StmtExt constructor here, so Cont's default is
     used. *)

  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = Option.to_list lib_source @ Cont.lib_sources
end
