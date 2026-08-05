open Base
open Ast
open ExtApi
open Util

(** Here, we implement an extension that adds support for Iris-style _prophecy variables_. This is what `--extension default` (equivalently, no `--extension` flag) activates -- it has no flag of its own, and is mutually exclusive with the ErrorCredits extension (`--extension eris`), since combining the two is not sound.

A prophecy variable denotes a value (or sequence of values) that will only be
observed at a future point during program execution. In particular, the value
may depend on non-deterministic choices (such as scheduler decisions) that will
be made between the current point of execution and the point when the value
will be observed. A prophecy variable allows one effectively to predict the
outcome of such future choices and reason about them before they occur
(e.g., via case analysis).

The extension implements:
  - a parametric type `Proph[T]` whose values represent multi-shot prophecies p predicting an unbounded sequence of values of type T,
  - a parametric type `Proph[T, 1]` whose values represent one-shot prophecies p predicting a single value of type T, resolvable at most once,
  - a command `proph_id, proph_val := new Proph[T]` for creating new multi-shot prophecies,
  - a command `proph_id, proph_val := new Proph[T, 1]` for creating new one-shot prophecies,
  - `Proph.proph(proph_id, value)` for asserting/inhaling/exhaling the prophecy resource (value: List[T] for multi-shot, T for one-shot -- which shape is expected is determined by proph_id's own Proph[...] type),
  - a command `Proph.resolve(proph_id, value);` for resolving prophecies.
*)


module ProphecyExt (Cont : ListApi) = struct
  (* Every hook defaults to Cont's (including ListFns, since Cont : ListApi); only the
     ones actually overridden below need a definition. *)
  include Cont

  (* Custom library to be included as part of this extension. The contents of `prophecyLib.rav` are appended to Raven's `Library` module. *)
  let lib_source = Some ("lib/ext/prophecyExt/prophecyLib.rav", [%blob "prophecyLib.rav"])

  (* Defining pre-fixed idents from the `Prophecy`/`Prophecy1` modules defined in prophecyLib.rav. These modules get added to Raven's `Library`, and thus can be accessed as `Library.Prophecy`/`Library.Prophecy1`. We instantiate one of these modules for each type T used in the program (once for its multi-shot uses, once for its one-shot uses). Kept as two separate functor modules -- each with its field declared as plain `Typ`, substituted with `List[T]`/`T` respectively at instantiation time (see `initialize_prophecy_module`) -- rather than as `List[Typ]`/`Typ` fields on one shared functor: writing `List[Typ]` directly against the functor's own abstract type parameter in prophecyLib.rav triggers a pre-existing bug in the module-instantiation/reification machinery where that field's `Frac$...` datatype silently goes undeclared in the generated SMT. *)
  module ProphPredefs = struct
    let proph_mod_ident = Ident.make Loc.dummy "Prophecy" 0
    let proph_mod_qi = QualIdent.from_list [Predefs.lib_ident; proph_mod_ident]
    let proph1_mod_ident = Ident.make Loc.dummy "Prophecy1" 0
    let proph1_mod_qi = QualIdent.from_list [Predefs.lib_ident; proph1_mod_ident]

    let field_ident one_shot =
      if one_shot then Ident.make Loc.dummy "prophecyValue1" 0
      else Ident.make Loc.dummy "prophecyValue" 0

    (* Custom prefixes used for generating Prophecy module names, kept distinct so a
       type T's multi-shot and one-shot instantiations never collide. Using `$` in
       Raven makes the ident safe from collisions with user-defined modules, because
       `$` is not supported by Raven's parser. *)
    let proph_mod_ident_prefix = "ProphecyMod$"
    let proph1_mod_ident_prefix = "ProphecyMod1$"
  end

  (* Type for Prophecy variables, parametric in the predicted element type. The bool
     records whether this is a one-shot ([true]) or multi-shot ([false]) prophecy --
     `Proph[T, 1]` vs `Proph[T]` at the surface level. *)
  type Type.type_ext +=
    | ProphId of bool

  (* Prophecy resource: `Proph.proph(p, v)`. Whether `v` is expected to be a `T` or
     a `List[T]` is determined at type-checking time from `p`'s own `Proph[...]`
     type; the bool payload records that answer for the later rewrite. *)
  type Expr.expr_ext +=
    | ProphResource of bool

  (* New statements:
      - generate new prophecies. bool represents whether it is a one-shot prophecy or a multi-shot prophecy.
      - resolve prophecies. bool likewise records one-shot vs multi-shot, determined during type-checking from the prophecy id's type.
  *)
  type Stmt.stmt_ext +=
    | NewProph of bool * type_expr
    | ResolveProph of bool

  (* This is what type_expr in Raven look like.
      The arguments to Type.mk_app in order:
      - ~loc: location information in source code used for error printing
      - ~ghost: indicates whether the type is a _ghost_ type, ie only part of proof, not the executable program.
      - (TypeExt (ProphId one_shot)): This is a type construct `Type.constr`, used to annotate types. Specifically, `TypeExt` denotes an "extension" type.
      - [typ]: The single type argument -- the type of the values this prophecy predicts.
  *)
  let proph_id_type ~loc ~one_shot typ = Type.mk_app ~loc ~ghost:true (TypeExt (ProphId one_shot)) [typ]

  (** AstDef *)

  (* Standard pattern: match on our constructors, defer the rest. *)
  let type_ext_to_name type_ext = match type_ext with
  | ProphId _ -> "Proph"
  | _ ->
    Cont.type_ext_to_name type_ext

  let expr_ext_to_string expr_ext =
    match expr_ext with
    | ProphResource _ -> "Proph.proph"
    | _ -> Cont.expr_ext_to_string expr_ext

  (* Standard format for printer functions. *)
  let pr_basic_stmt_ext ppf ext expr_list =
    let open Stdlib.Format in
    match ext, expr_list with
    | (NewProph (b, typ)), [proph_id; proph_val] ->
      fprintf ppf "@[[EXT] %a, %a@ :=@ new Proph[typ:%a%s]@]" Expr.pr proph_id Expr.pr proph_val Type.pr typ (if b then ", 1" else "")

    (* Make sure to have a case for malformed arguments; ensures we catch all our cases. *)
    | NewProph _, _ ->
      Error.internal_error Loc.dummy "wrong number of arguments for new Proph(...)"


    | ResolveProph _, [proph_id; resolve_val] ->
      fprintf ppf "@[[EXT] Proph.resolve(%a -> %a)@]" Expr.pr proph_id Expr.pr resolve_val

    | ResolveProph _, _ ->
      Error.internal_error Loc.dummy "wrong number of arguments for Proph.resolve(...)"

    | _ -> Cont.pr_basic_stmt_ext ppf ext expr_list

  (* This is almost always expected to be empty. Only to be used if one stores variables/names within the Stmt _constructor_. Typically all the additional arguments are stored as stmt_args *)
  let basic_stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | NewProph _ -> Set.empty (module QualIdent)
    | ResolveProph _ -> Set.empty (module QualIdent)
    | _ -> Cont.basic_stmt_ext_symbols stmt_ext

  (* This one is more nuanced. Given the statement extension and all its expression arguments (ie the entire statement), we are supposed to return a list of local variables that are modified.

  This is used internally during the SSA transformation to determine whether to redefine a local var.
  *)
  let basic_stmt_ext_local_vars_modified stmt_ext exprs =
    match stmt_ext, exprs with
    | NewProph _, [proph_id; proph_val] ->
      if Expr.is_ident proph_val then
        (* We only return `proph_val` if it is an `ident`, or a local variable (as opposed to a `qual_ident` if it were a global `val`) *)
        [Expr.to_ident proph_id; Expr.to_ident proph_val]
      else
        (* Must be a bit careful with `Expr.to_ident`. This method crashes if underlying expression is not an ident *)
        [Expr.to_ident proph_id]

    (* Catching general arguments *)
    | NewProph _, _ ->
      Error.internal_error Loc.dummy "wrong number of arguments for new Proph(...)"

    | ResolveProph _, [proph_id; resolve_val] ->
      (* In this case, no _variables_ are being updated, only resources are manipulated.  *)
      []

    | ResolveProph _, _ ->
      Error.internal_error Loc.dummy "wrong number of arguments for Proph.resolve(...)"

    | _ -> Cont.basic_stmt_ext_local_vars_modified stmt_ext exprs

  (* Utility function to generate canonical module name. Using `Type.to_string` to convert the underlying type to a string. Using `ProgUtils.serialize` to make sure the name is compatible with SMT. Using `Ident.make` instead of `Ident.fresh` because we want all references to this ident to be to the same module. `one_shot` picks which of the two prefixes to use, so a type T's multi-shot and one-shot instantiations never collide.  *)
  let prophecy_module_ident ~loc ~one_shot typ =
      let prefix = if one_shot then ProphPredefs.proph1_mod_ident_prefix else ProphPredefs.proph_mod_ident_prefix in
      let prophecy_mod_string = prefix ^ Type.to_string typ in
      Ident.make loc (ProgUtils.serialize prophecy_mod_string) 0

  (* Utility function to generate fully qualified ident (qual_ident) to refer to the prophecy module. Computing the right scope to add the prophecy module. This only matters if abstract and custom types are used to create prophecy variables, otherwise the Prophecy module gets added to the root. But Raven's module system adds certain restrictions to where types and objects can and can't be defined or used. *)
  let prophecy_module_from_type_qi ~loc ~one_shot typ =
    (* Type.symbols returns a set of all user-defined types that are referenced in a given type. *)
    let symbols = Type.symbols typ in
    (* This turns out to be the right place to add the new module. *)
    let module_scope = ProgUtils.largest_common_prefix_qi symbols in

    (* Construct the new qual_ident, by combining `module_scope` and `prophecy_module_ident` *)
    QualIdent.append module_scope (prophecy_module_ident ~loc ~one_shot typ)

  (* We need to return the list of fields that this command depends on. Since we model prophecy resources using a field defined in `prophecyLib.rav`, that field gets updated. The qual_ident for this is built by combining  *)
  let basic_stmt_ext_fields_accessed stmt_ext exprs =
    match stmt_ext, exprs with
    | NewProph (one_shot, typ), _ ->
      let proph_mod_qi = prophecy_module_from_type_qi ~loc:Loc.dummy ~one_shot typ in
      let proph_field_ident = ProphPredefs.field_ident one_shot in

      (* Append the fixed proph_field_ident (specified in prophecyLib.rav), to the specific instantiation of the prophecy module.  *)
      [QualIdent.append proph_mod_qi proph_field_ident]

      (* Same field getting modified when resolving a prophecy. Resolve's second argument is always of the predicted element type T (never List[T], one-shot or not), so we can read it straight off `resolve_val`'s type -- same as before genericity. *)
    | ResolveProph one_shot, [proph_id; resolve_val] ->
      let typ = Expr.to_type resolve_val in
      let proph_mod_qi = prophecy_module_from_type_qi ~loc:Loc.dummy ~one_shot typ in
      let proph_field_ident = ProphPredefs.field_ident one_shot in

      [QualIdent.append proph_mod_qi proph_field_ident]

    | ResolveProph _, _ ->
      Error.internal_error Loc.dummy "wrong number of arguments for Proph.resolve(...)"

    | _ -> Cont.basic_stmt_ext_fields_accessed stmt_ext exprs

  (* pr_stmt_ext/stmt_ext_*: no top-level StmtExt constructors here, so Cont's default
     is used. *)

  let type_ext_is_recognized type_ext =
    match type_ext with
    | ProphId _ -> true
    | _ -> Cont.type_ext_is_recognized type_ext

  let expr_ext_is_recognized expr_ext =
    match expr_ext with
    | ProphResource _ -> true
    | _ -> Cont.expr_ext_is_recognized expr_ext

  let stmt_ext_is_recognized stmt_ext =
    match stmt_ext with
    | NewProph _ | ResolveProph _ -> true
    | _ -> Cont.stmt_ext_is_recognized stmt_ext

  (* Both lower to ghost blocks over the ghost prophecy field: a resolution has to
     sit alongside the physical step it is attached to (Iris's `Resolve e p v`),
     so charging it a step of its own would make exactly that pattern impossible. *)
  let stmt_ext_atomicity stmt_ext =
    match stmt_ext with
    | NewProph _ | ResolveProph _ -> Stmt.NoStep
    | _ -> Cont.stmt_ext_atomicity stmt_ext

  (* contract_ext_is_recognized: no contract_ext constructors here, so Cont's default
     is used. *)


  (* Rewriter *)

  (* These methods are used if our constructors contain _type_expr_'s.

    In this rare case, the NewProph constructor contains a type expression.

    ~f refers to a function which *rewrites* types. This is part of Raven's internal infrastructure of rewrites.

    expr_ext_rewrite_types: neither ProphResource nor ResolveProph store a type_expr
    of their own (their element type is always recoverable from their expr
    arguments' types at rewrite time -- see [rewrite_expr_ext]/[rewrite_basic_stmt_ext]
    below), so Cont's default is used.
  *)
  let basic_stmt_ext_rewrite_types ~f stmt_ext =
    let open Rewriter.Syntax in
    match stmt_ext with
    | NewProph (b, tp_expr) ->
      (* We run `f` on the type_expr we contain, and re-build the stmt_ext constr. *)
      let+ tp_expr = f tp_expr in
      NewProph (b, tp_expr)
    |_ -> Cont.basic_stmt_ext_rewrite_types ~f stmt_ext

  (* stmt_ext_rewrite: no top-level StmtExt constructor here, so Cont's default is
     used. *)


  (* Typing *)

  (* Perform type-checking on type_expr. The underlying type is stored in the AST as follows:
    Type.App (TypeExt type_ext, type_args, type_attr)

    type_check_type_expr_functs contains functions from `Typing.ml` useful for type-checking. These are defined in ExtApi.ml.
  *)
  let type_check_type_expr type_ext type_args type_attr type_check_type_expr_functs =
    let open Rewriter.Syntax in
    match type_ext, type_args with
    | ProphId one_shot, [t] ->
      (* Recursively type-check the element type argument, same as List[T]. Making sure to set Type.ghost. *)
      let+ t = type_check_type_expr_functs.process_type_expr t in
      Type.App (TypeExt (ProphId one_shot), [t], type_attr) |> Type.set_ghost true

    | ProphId _, _ ->
      (* Raise type_error otherwise. *)
      Error.type_error type_attr.Type.type_loc "Proph[...] type expects exactly one type argument (the element type)"

    | _ -> Cont.type_check_type_expr type_ext type_args type_attr type_check_type_expr_functs

  (* Type-checking of expressions. The underlying expression in the AST that we are type-checking is:
      Expr.App ((ExprExt expr_ext), expr_list, expr_attr)

    expected_typ contains typing hints from the surrounding env, but is often `Type.any`.
  *)
  let type_check_expr (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr : Expr.expr_attr) (expected_typ: type_expr) (type_check_expr_functs: type_check_expr_functs) =
    let open Rewriter.Syntax in
    let loc = expr_attr.expr_loc in

    match expr_ext, expr_list with
    (* These are the arguments we expect. *)
    | ProphResource _, [proph_id_expr; value_expr] ->
      (* Type-checking proph_id_expr against `Type.any`: its declared type (some
         `Proph[T]`/`Proph[T, 1]`) tells us both the element type T and whether the
         second argument should be a `T` (one-shot) or a `List[T]` (multi-shot). *)
      let* proph_id_expr = type_check_expr_functs.process_expr proph_id_expr (Type.any |> Type.set_ghost true) in

      let one_shot, elem_typ = match Expr.to_type proph_id_expr with
        | Type.App (TypeExt (ProphId one_shot), [t], _) -> one_shot, t
        | tp -> Error.type_error loc ("Proph.proph(...) expects its first argument to be a Proph[...] value; found: " ^ (Type.to_string tp))
      in

      let expected_value_typ =
        if one_shot then elem_typ |> Type.set_ghost true
        else Cont.ListFns.mk_list_tp loc elem_typ |> Type.set_ghost true
      in

      (* Type-checking value_expr *)
      let* value_expr = type_check_expr_functs.process_expr value_expr expected_value_typ in

      Rewriter.return @@ (Expr.mk_app ~loc ~typ:Type.perm (ExprExt (ProphResource one_shot)) [proph_id_expr; value_expr])

    (* Incorrect number of arguments found; raise a type_error. *)
    | ProphResource _, _ ->
      Error.type_error loc "Proph.proph(...) called with incorrect number of arguments"

    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ type_check_expr_functs


  (* Type-checking of stmts. The underlying stmt in the AST is represented as:
      Stmt.{
        stmt_desc = Basic (BasicStmtExt (stmt_ext, expr_list));
        stmt_loc = stmt_loc;
      }

    `disam_tbl` is a data structure used to disambiguate local variables occuring in different subscopes by assigning a unique `ident_num` to each local variable. There is no need to understand how this works or to manipulate this manually. Some functions require and return this argument, which indicates how this must be used. However, care must be made to update and return this correctly.

    This function returns a `Stmt.basic_stmt_desc`. This is an object like:
      (BasicStmtExt (stmt_ext, expr_list))
    In addition, a `disam_tbl` must be returned.
    `type_check_stmt_functs` is again a set of functions from `typing.ml` that are useful for type-checking statements.
  *)
  (* type_check_contract_ext/check_contract_ext_group_compatible/
     contract_ext_to_string: no contract_ext constructors here, so Cont's default is
     used. *)

  let type_check_basic_stmt call_decl (stmt_ext : Stmt.stmt_ext) (expr_list: expr list) (stmt_loc: Loc.t) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : ExtApi.type_check_stmt_functs)
  :
      (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t =

    (* A Raven debug statement. *)
    Logs.debug (fun m -> m "[EXT] ProphecyExt.type_check_basic_stmt: started");

    let open Rewriter.Syntax in
    (* Determining whether we are in a ghost scope. Certain actions aren't allowed in ghost scopes, such as making concrete program steps, procedure calls, etc. *)
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    match stmt_ext, expr_list with
      (* ```proph_id, proph_val := new Proph[typ]``` / ```new Proph[typ, 1]``` *)
    | NewProph (oneshot_b, typ), [proph_id; proph_val] ->
      (* Type-check `proph_id` against the Proph[typ]/Proph[typ, 1] type -- this both
         checks/binds `proph_id` and, if it was already declared with a different
         Proph[...] type, catches the mismatch here. From `type_check_basic_stmt`, we must call `disambiguate_process_expr, instead of `process_expr` to make sure we use `disam_tbl` consistently.  *)
      let* proph_id = type_check_stmt_functs.disambiguate_process_expr proph_id (proph_id_type ~loc:stmt_loc ~one_shot:oneshot_b typ) disam_tbl

      in

      let proph_val_typ = if oneshot_b then
        (* If it is a one-shot prophecy, the type for `proph_val` is same as the type annotation on `new Proph[..., 1]`, ie `typ` *)
        typ |> Type.set_ghost true
      else
        (* Else, the type for `proph_val` is `List[typ]`. We use `Cont.ListFns.mk_list_tp` to construct this List type. *)
        Cont.ListFns.mk_list_tp stmt_loc typ |> Type.set_ghost true
      in

      begin match Expr.is_ident proph_val with
      | false ->
        (* Must be called on a local variable; otherwise type_error. *)
        Error.type_error stmt_loc "new Proph(...) must be assigned to a local variable"

      | true ->
        (* Type-checking proph_val. *)
        let* proph_val = type_check_stmt_functs.disambiguate_process_expr proph_val proph_val_typ disam_tbl in

        (* Everything checks out. Constructing final `Stmt.basic_stmt_desc` to return.
          Making sure to use updated and type-checked values `proph_id` and `proph_val`. not stale values.
        *)
        (Stmt.BasicStmtExt (
          NewProph (oneshot_b, typ), [proph_id; proph_val]
        ), disam_tbl) |> Rewriter.return
      end
    | NewProph _, _ ->
      Error.type_error stmt_loc "new Proph(...) called with incorrect number of arguments"

      (* ```Proph.resolve(proph_id, resolve_value)``` *)
    | ResolveProph _, [proph_id; resolve_value] ->
      (* Type-checking proph_id against `Type.any`: its declared Proph[...] type tells
         us the predicted element type T and whether this is a one-shot or multi-shot
         prophecy. *)
      let* proph_id = type_check_stmt_functs.disambiguate_process_expr proph_id (Type.any |> Type.set_ghost true) disam_tbl in

      let one_shot, elem_typ = match Expr.to_type proph_id with
        | Type.App (TypeExt (ProphId one_shot), [t], _) -> one_shot, t
        | tp -> Error.type_error stmt_loc ("Proph.resolve(...) expects its first argument to be a Proph[...] value; found: " ^ (Type.to_string tp))
      in

      let* resolve_value = type_check_stmt_functs.disambiguate_process_expr resolve_value (elem_typ |> Type.set_ghost true) disam_tbl in

      (* Constructing final return `Stmt.basic_stmt_desc` *)
      (Stmt.BasicStmtExt (
        ResolveProph one_shot, [proph_id; resolve_value]
      ), disam_tbl) |> Rewriter.return

    | ResolveProph _, _ ->
      Error.type_error stmt_loc "Proph.resolve(...) called with incorrect number of arguments"

    | _ -> Cont.type_check_basic_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl type_check_stmt_functs

  (* type_check_stmt_ext: no top-level StmtExt constructor here, so Cont's default is
     used. *)


  (* Rewrites *)

  (** Safely initialize prophecy module and return its qual_ident. In particular, this function is idempotent, so can be called whenever need to convert a type_expr into its corresponding prophecy_module_qual_ident. `one_shot` picks between the `Prophecy`/`Prophecy1` library functors, and thus between instantiating with `Typ := List[typ]` (multi-shot) or `Typ := typ` (one-shot).

  This function is used to take any type_expr, check if a Prophecy(1) module has been instantiated for this type, and if not, then define and instantiate such a Prophecy(1) module for that type.

  *)
  let initialize_prophecy_module loc ~one_shot (typ: type_expr): qual_ident Rewriter.t =
    let open Rewriter.Syntax in

    (* This is the canonical qual_ident that a type's prophecy_module must be at. *)
    let proph_module_qi = prophecy_module_from_type_qi ~loc ~one_shot typ
    in

    Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Looking up proph_module_qi: %a" QualIdent.pr proph_module_qi);
    let* lookup = Rewriter.resolve_and_find_opt proph_module_qi in

    match lookup with
    | Some _ ->
      (* Found an existing module there. Simply return the qual_ident. *)
      Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Look-up succeeded for proph_module_qi: %a" QualIdent.pr proph_module_qi);
      Rewriter.return proph_module_qi

    | None ->
      Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Proph module not found. Initializing... proph_module_qi: %a" QualIdent.pr proph_module_qi);
      (* Proph module not found. Initializing... *)

      (* `proph_module_insert_scope`, and `proph_module_reference_scope` refer to two different scope.
        - The first is the location where the instantiation of `Library.Prophecy`/`Library.Prophecy1` module must be inserted.
        - The second is part of the fully qualified ident from which to reference the aforementioned module.

        The reason these might be different, is if we have for instance:
          ```raven

            interface A
            module F[C: A] { type T = ...; }
            module A0 : A
            module M = F[A0]

             ...new Proph[M.T]; ...
          ```

        In this case, we add the Prophecy module inside the definition of `F`, the concretely defined higher-order module, since we cannot add it to `M` as `M` is represented abstractly inside Raven's symbol table. However, we will refer to the Prophecy module as `M.proph$T`, etc. Thus:
          insert_scope = F
          reference_scope = M
      *)
      let* proph_module_insert_scope, proph_module_reference_scope =
        let largest_prefix = QualIdent.pop proph_module_qi in

        (* Rewriter.resolve_and_find_opt returns whether the `largest_prefix` exists. This is the location where the prophecy module must eventually be added. *)
        let* result = Rewriter.resolve_and_find_opt largest_prefix in
        begin match result with
        | None ->
          Error.internal_error loc "could not find the enclosing scope while initializing the prophecy module"
        | Some (qi, (name, symbol, _)) ->
          (* This returns an internal symbol_tbl object. This includes a potential renaming map, which is not too important. *)
          Rewriter.return (name, qi)
        end
      in

      (* We generate a module satisfying the `Library.Type` interface, with the right rep type: `List[typ]` for a multi-shot prophecy, or plain `typ` for a one-shot prophecy (its field holds a single predicted value, not a list of them). The field itself stays declared as plain `Typ` in prophecyLib.rav; it is this instantiation argument -- not a `List[Typ]` written against the functor's own abstract parameter -- that gives the multi-shot field its list shape (see the module-level doc comment on `ProphPredefs` for why). *)
      let* type_module_qi =
        let rep_typ = if one_shot then typ else Cont.ListFns.mk_list_tp loc typ in

        (* Similarly, a canonical qual_ident exists for the `type_module` too. *)
        let type_module_canonical_qi =
          let mod_name_string = ProgUtils.tp_mod_ident_prefix ^ Type.to_string rep_typ in
          let type_module_ident = Ident.make loc (ProgUtils.serialize mod_name_string) 0 in
          QualIdent.append proph_module_reference_scope type_module_ident
        in

        let* resolve_result = Rewriter.resolve_opt type_module_canonical_qi in

        match resolve_result with
        | Some _ ->
          Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Type Module found. type_module_qi: %a" QualIdent.pr type_module_canonical_qi);
          Rewriter.return type_module_canonical_qi
        | None ->
          (* If the type_module is not found, we us `ProgUtils.intros_type_module_qi` to build and add this module to the AST. *)
          Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Type module also not found. Initializing... type_module_qi: %a" QualIdent.pr type_module_canonical_qi);
            let+ introd_type_module_qi =
              ProgUtils.intros_type_module ~loc ~scope:proph_module_insert_scope ~f:!(Rewriter.process_symbol_ref) rep_typ in

            Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Type module successfully initialized. type_module_qi: %a" QualIdent.pr type_module_canonical_qi);
            type_module_canonical_qi
      in

      (* Finally, we generate the name for the final Prophecy module. *)
      let proph_module_ident = prophecy_module_ident ~loc ~one_shot typ in
      let proph_functor_qi = if one_shot then ProphPredefs.proph1_mod_qi else ProphPredefs.proph_mod_qi in

      (* Definition of module instantiation. This is equivalent to the Raven syntax:
        ```
          proph_module_ident = ProphPredefs.proph_mod_qi [ type_module_qi ]
        ```
       *)
      let proph_module_inst = Module.ModInst {
        mod_inst_name = proph_module_ident;
        mod_inst_type = proph_functor_qi;
        mod_inst_def = Some (proph_functor_qi, [Module.ModArg type_module_qi]);
        mod_inst_is_interface = false;
        mod_inst_is_free = false;
        mod_inst_loc = loc;
      } in

      Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: proph_module_ident = %a; about to introduce" Ident.pr proph_module_ident);

      (* Finally, we call the `Rewriter.introduce_typecheck_symbol_at_scope'` to type-check this symbol, and finally introduce the type-checked symbol to the AST. If the type-check fails, the program crashes, so be careful! *)
      let* _proph_module_inst_qi =
        Rewriter.introduce_typecheck_symbol_at_scope' ~loc proph_module_inst proph_module_insert_scope in

      Rewriter.return proph_module_qi

    (* Now, we finally come to rewriting.

    We replace any reference to `Proph[T]` type with references (`Ref`s). This is because prophecies are modeled using resources, and in Raven only `Ref`s can have resources associated (one per field). The type argument (and shot-kind) only matter for picking which field to associate; the erased runtime representation is the same `Ref` either way.

    *)
  let rewrite_type_ext (type_ext: Type.type_ext) (tp_list: type_expr list) (loc: location) : type_expr Rewriter.t =
    match type_ext, tp_list with
    | ProphId _, [_] ->
      Rewriter.return Type.ref
    | ProphId _, _ ->
      Error.type_error loc "Proph[...] type expects exactly one type argument (the element type)"
    | _ -> Cont.rewrite_type_ext type_ext tp_list loc



  (* Rewriting expressions. *)
  let rewrite_expr_ext (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr: Expr.expr_attr) =
    let open Rewriter.Syntax in
    let loc = expr_attr.expr_loc in
    match expr_ext, expr_list with
    | ProphResource one_shot, [proph_id; value] ->
      let* proph_type =
        if one_shot then
          (* `value`'s type already *is* the predicted element type. *)
          !Rewriter.expand_type_expr_ref (Expr.to_type value)
        else
          (* Extracting element type from the List[.] type of `value`. *)
          let elem_tp_opt = Cont.ListFns.list_tp_to_elem_typ (Expr.to_type value) in
          begin match elem_tp_opt with
          (* A `List[.]` type NOT found. That's an internal error -- already validated during type-checking. *)
          | None -> Error.internal_error loc ("expected the prophecy resource's value to be a List (already validated during type-checking); found: " ^ (Type.to_string (Expr.to_type value)))
          (* Okay, everything checks out. *)
          | Some elem_typ ->
            (* We call `Typing.expand_type_expr` (via the Rewriter.expand_type_expr_ref), to make sure we get uniform, fully expanded types. *)
            !Rewriter.expand_type_expr_ref elem_typ
          end
      in

      (* Initialize prophecy_module if it doesn't exist. No worries if it does. *)
      let* proph_module_qi = initialize_prophecy_module loc ~one_shot proph_type in
      let prophecy_field_qi = QualIdent.append proph_module_qi (ProphPredefs.field_ident one_shot) in

      (* Rewriter.find_and_reify_field takes the `qual_ident` for a field, finds it in the symbol table, does any Module substitutions to get a concrete symbol (reification), then unpacks the underlying `FieldDef` symbol.  *)
      let* prophecy_field = Rewriter.find_and_reify_field prophecy_field_qi in

      (* Finally, replace the `ProphResource` with its equivalent separation-logic resource, constructed with the `Own` constructor.

      Arguments to the Own constructor are:
      - The expression for the Ref.
      - An expression for the field.
      - A value expression.
      - A real number to denote fractional ownership. Here we use 1.0 to denote total ownership.

      *)
      Expr.mk_app ~typ:Type.perm ~loc Own [
        proph_id;
        Expr.mk_var ~typ:prophecy_field.field_type prophecy_field_qi;
        value;
        Expr.mk_real ~loc 1.0;
      ] |> Rewriter.return

    | _ -> Cont.rewrite_expr_ext expr_ext expr_list expr_attr


  (* contract_ext_rewrite_exprs/rewrite_contract_ext_call/rewrite_callable_entry/
     rewrite_contract_ext_loop_transfer: no contract_ext constructors here, so Cont's
     default is used. *)

  (* Rewriting Statements *)
  let rewrite_basic_stmt_ext (stmt_ext: Stmt.stmt_ext) (expr_list: expr list) loc: Stmt.t Rewriter.t =
    let open Rewriter.Syntax in

    Logs.debug (fun m -> m "[EXT] ProphecyExt.rewrite_stmt: Starting");

    match stmt_ext, expr_list with
    (* ```proph_id, proph_val := new Proph[typ]``` / ```new Proph[typ, 1]``` *)
    | NewProph (oneshot_b, typ), [proph_id; proph_val] ->

      let* () = Rewriter.Logs.debug (fun printers m -> m "[EXT] ProphecyExt.rewrite_stmt: NewProph(one_shot:%b; type:%a)" oneshot_b printers.pr_type typ) in

      (* using `initialize_prophecy_module` to generate the proph_module_qi. *)
      let* proph_module_qi = initialize_prophecy_module loc ~one_shot:oneshot_b typ in
      let prophecy_field_qi = QualIdent.append proph_module_qi (ProphPredefs.field_ident oneshot_b) in

      let* prophecy_field_symbol = Rewriter.find_and_reify_field prophecy_field_qi in

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
        Stmt.mk_inhale_expr ~loc
        ~cmnt:("[EXT] ProphExt: Inhale stmt for new Proph()")
        (Expr.mk_app ~loc ~typ:Type.perm Expr.Own [
          proph_id;
          Expr.mk_var ~typ:prophecy_field_symbol.field_type prophecy_field_qi;
          proph_val;
          Expr.mk_real 1.0;
        ])
      in

      (* Create a block_stmt containing all the statements. This block is indeed a ghost block, so setting ~ghost:true *)
      Rewriter.return (Stmt.mk_block_stmt ~loc ~ghost:true
        [havoc_stmt1; havoc_stmt2; proph_new_stmt]
      )

    | NewProph _, _ ->
            Error.internal_error loc "unexpected argument count for new Proph(...) at rewrite time (already validated during type-checking)"

    (* For ```Proph.resolve(proph_id, resolve_value)``` statements *)
    | ResolveProph one_shot, [proph_id; resolve_value] ->
      (* Resolve's second argument is always of the predicted element type T (never
         List[T], one-shot or not), so `typ` is read straight off it. *)
      let typ = Expr.to_type resolve_value in
      let* proph_module_qi = initialize_prophecy_module loc ~one_shot typ in
      let prophecy_field_qi = QualIdent.append proph_module_qi
        (Ident.set_loc loc (ProphPredefs.field_ident one_shot))
      in

      let* prophecy_field = Rewriter.find_and_reify_field prophecy_field_qi in

      (* The type of the prophecy field is `List[typ]` for a multi-shot prophecy, or
         plain `typ` for a one-shot one. *)
      let proph_read_tp = if one_shot then typ else Cont.ListFns.mk_list_tp loc typ in

      (* Creating new local variable to store value of `proph_id.prophecy_field` *)
      let proph_read_var_def, proph_read_var_ident =
        (* Ident.fresh to generate new fresh ident. *)
        let proph_read_var_ident = Ident.fresh loc "$proph_read" in

        (* Creating a `var_def` object, used to introduce the new local variable. *)
        Stmt.{
          var_decl = Type.mk_var_decl ~ghost:true proph_read_var_ident ~loc proph_read_tp ;
          var_init = None;
          var_is_free = NotFree;
        }, proph_read_var_ident
      in

      let* proph_id_var_def = Rewriter.find_and_reify_var (Expr.to_qual_ident proph_id) in

      let* _ = Rewriter.introduce_symbol (VarDef proph_read_var_def) in

      (* Constructing field_read stmt, by hand. Equivalent to:
        ```proph_read_var := proph_id.prophecy_field_qi;```
      *)
      let field_read_stmt =
        let field_read_desc = Stmt.{
          field_read_lhs=QualIdent.from_ident proph_read_var_ident;
          field_read_field=prophecy_field_qi;
          field_read_ref= Expr.set_loc (Expr.from_var_decl proph_id_var_def.var_decl) loc;
          field_read_is_init=true;
        } in

        Stmt.{stmt_desc = Basic (FieldRead field_read_desc); stmt_loc = loc; }
      in

      if one_shot then
        (* One-shot: assert the resolved value matches the predicted one, then
           *exhale* the resource -- with no matching re-inhale, ownership of it is
           spent for good, so a second `Proph.resolve` on the same `proph_id` has no
           permission left to read the field. That is what makes a one-shot
           prophecy actually resolvable at most once, rather than merely by
           convention. *)
        let prophetic_assertion =
          Stmt.mk_assume_expr ~loc
          ~cmnt:("[EXT] ProphecyExt: Prophecising Assertion")
          (Expr.mk_eq
            resolve_value
            (Expr.from_var_decl proph_read_var_def.var_decl)
            )
        in

        let exhale_stmt =
          Stmt.mk_exhale_expr ~loc
          ~cmnt:("[EXT] ProphecyExt: one-shot prophecy resource is fully consumed by resolve")
          (Expr.mk_app ~loc ~typ:Type.perm Expr.Own [
            Expr.from_var_decl proph_id_var_def.var_decl;
            Expr.mk_var ~typ:prophecy_field.field_type prophecy_field_qi;
            Expr.from_var_decl proph_read_var_def.var_decl;
            Expr.mk_real ~loc 1.0;
          ])
        in

        Rewriter.return (Stmt.mk_block_stmt ~loc ~ghost:true
          [field_read_stmt; prophetic_assertion; exhale_stmt])
      else

      (* Add assumption about the prophecy, as an `assume` stmt.
        ```assume resolve_value = List.hd(proph_read_var)```
      *)
      let prophetic_assertion =
        Stmt.mk_assume_expr ~loc
        ~cmnt:("[EXT] ProphecyExt: Prophecising Assertion")
        (Expr.mk_eq
          resolve_value
          (Cont.ListFns.ls_hd loc (Expr.from_var_decl proph_read_var_def.var_decl))
          )
      in

      (* ```assume List.len(proph_read_var) > 2``` *)
      let list_non_empty =
        Stmt.mk_assume_expr ~loc
        ~cmnt:("[EXT] ProphecyExt: Assuming remaining prophecy stream non-empty")
        (Expr.mk_app ~loc ~typ:Type.bool Gt
          [(Cont.ListFns.ls_len loc (Expr.from_var_decl proph_read_var_def.var_decl));
          Expr.mk_int 2]
        )
      in

      (* ```List.tl(proph_read_var)``` *)
      let field_write_val =
        Cont.ListFns.ls_tl loc (Expr.from_var_decl proph_read_var_def.var_decl)
      in

      (* ```proph_id.prophecy_field_qi := field_write_val;``` *)
      let field_write_stmt =
        let field_write_desc = Stmt.{
          field_write_ref = Expr.from_var_decl proph_id_var_def.var_decl;
          field_write_field = prophecy_field_qi;
          field_write_val = field_write_val
        } in

        Stmt.{stmt_desc = Basic (FieldWrite field_write_desc); stmt_loc = loc;}
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc ~ghost:true
        [field_read_stmt; prophetic_assertion; list_non_empty; field_write_stmt])

    | ResolveProph _, _ ->
      Error.internal_error loc "unexpected argument count for Proph.resolve(...) at rewrite time (already validated during type-checking)"

    | _ -> Cont.rewrite_basic_stmt_ext stmt_ext expr_list loc

  (* rewrite_stmt_ext: no top-level StmtExt constructor here, so Cont's default is
     used. *)


  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
end
