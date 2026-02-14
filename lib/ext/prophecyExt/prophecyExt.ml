open Base
open Ast
open ExtApi
open Util

(** Here, we implement an extension that adds support for Iris-style _prophecy variables_. This extension can be enabled with the 
  `--extension prophecy`
command-line argument

A prophecy variable denotes a value (or sequence of values) that will only be 
observed at a future point during program execution. In particular, the value
may depend on non-deterministic choices (such as scheduler decisions) that will
be made between the current point of execution and the point when the value 
will be observed. A prophecy variable allows one effectively to predict the 
outcome of such future choices and reason about them before they occur 
(e.g., via case analysis).

The extension implements:
  - a new parametric type `Proph[T]` whose values represent prophecies p predicting values of type T, 
  - a command `proph_id, proph_val := Proph.new[T];` for creating new sequence prophecies.
  - a command `proph_id, proph_val := Proph.new_1[T];` for creating new one-shot prophecies
  - a command `Proph.resolve(proph_id, value);` for resolving prophecies.
*)


module ProphecyExt (Cont : ListApi) = struct
  (* Custom library to be included as part of this extension. The contents of `prophecyLib.rav` are appended to Raven's `Library` module. *)
  let lib_source = Some ("prophecyLib.rav", [%blob "prophecyLib.rav"])
  let local_vars = []

  (* Defining pre-fixed idents from `Prophecy` module defined in prophecyLib.rav. This module gets added to Raven's `Library`, and thus can be accessed as `Library.Prophecy`. We instantiate this module for each type used in the program.  *)
  module ProphPredefs = struct
    let proph_mod_ident = Ident.make Loc.dummy "Prophecy" 0
    let proph_mod_qi = QualIdent.from_list [Predefs.lib_ident; proph_mod_ident]
    let field_ident = Ident.make Loc.dummy "prophecyValue" 0

    (* Custom Prefix used for generating Prophecy Module names. Using `$` in Raven makes the ident safe from collisions with user-defined modules, because `$` is not supported by Raven's parser. *)
    let proph_mod_ident_prefix = "ProphecyMod$" 
  end

  (* Type for Prophecy variables. *)
  type Type.type_ext +=
    | ProphId

  (* Prophecy Resource *)
  type Expr.expr_ext +=
    | ProphResource

  (* New statements: 
      - generate new prophecies. bool represents whether it is a one-shot prophecy or a sequence prophecy.
      - resolve prophecies.
  *)
  type Stmt.stmt_ext +=
    | NewProph of bool * type_expr
    | ResolveProph

  (* This is what type_expr in Raven look like. 
      The arguments to Type.mk_app in order:
      - ~loc: location information in source code used for error printing
      - ~ghost: indicates whether the type is a _ghost_ type, ie only part of proof, not the executable program.
      - (TypeExt ProphId): This is a type construct `Type.constr`, used to annotate types. Specifically, `TypeExt` denotes an "extension" type.
      - []: This is a list of arguments the type constructor takes. Polymorphic types such as `Set` and `Map` use these arguments.
  *)
  let proph_id_type ~loc = Type.mk_app ~loc ~ghost:true (TypeExt ProphId) []

  (* This is to provide access to the ListExt API  to other modules depending on this module, since other extensions rely on the ListExt. *)
  module ListFns = Cont.ListFns

  (** AstDef *)

  (* Standard pattern: match on our constructors, defer the rest. *)
  let type_ext_to_name type_ext = match type_ext with
  | ProphId -> "Proph"
  | _ -> 
    Cont.type_ext_to_name type_ext

  let expr_ext_to_string expr_ext =
    match expr_ext with 
    | ProphResource -> "Proph.prophecy"
    | _ -> Cont.expr_ext_to_string expr_ext

  (* Standard format for printer functions. *)
  let pr_stmt_ext ppf ext expr_list = 
    let open Stdlib.Format in
    match ext, expr_list with
    | (NewProph (b, typ)), [proph_id; proph_val] ->
      fprintf ppf "@[[EXT] %a, %a@ :=@ Proph.new%s[typ:%a]@]" Expr.pr proph_id Expr.pr proph_val (if b then "_1" else "") Type.pr typ

    (* Make sure to have a case for malformed arguments; ensures we catch all our cases. *)
    | NewProph _, _ ->
      Error.internal_error Loc.dummy "[EXT] ProphecyExt.pr_stmt_ext: wrong number of arguments called for NewProph"

    
    | ResolveProph, [proph_id; resolve_val] ->
      fprintf ppf "@[[EXT] Proph.resolve(%a -> %a)@]" Expr.pr proph_id Expr.pr resolve_val 

    | ResolveProph, _ ->
      Error.internal_error Loc.dummy "[EXT] ProphecyExt.pr_stmt_ext: wrong number of arguments called for ResolveProph"

    | _ -> Cont.pr_stmt_ext ppf ext expr_list

  (* This is almost always expected to be empty. Only to be used if one stores variables/names within the Stmt _constructor_. Typically all the additional arguments are stored as stmt_args *)
  let stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | NewProph _ -> Set.empty (module QualIdent)
    | ResolveProph -> Set.empty (module QualIdent)
    | _ -> Cont.stmt_ext_symbols stmt_ext

  (* This one is more nuanced. Given the statement extension and all its expression arguments (ie the entire statement), we are supposed to return a list of local variables that are modified.
  
  This is used internally during the SSA transformation to determine whether to redefine a local var.
  *)
  let stmt_ext_local_vars_modified stmt_ext exprs =
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
      Error.internal_error Loc.dummy "[EXT] ProphecyExt: wrong number of arguments called for NewProph"

    | ResolveProph, [proph_id; resolve_val] ->
      (* In this case, no _variables_ are being updated, only resources are manipulated.  *)
      []

    | ResolveProph, _ ->
      Error.internal_error Loc.dummy "[EXT] ProphecyExt: wrong number of arguments called for ResolveProph"

    | _ -> Cont.stmt_ext_local_vars_modified stmt_ext exprs

  (* Utility function to generate canonical module name. Using `Type.to_string` to convert the underlying type to a string. Using `ProgUtils.serialize` to make sure the name is compatible with SMT. Using `Ident.make` instead of `Ident.fresh` because we want all references to this ident to be to the same module.  *)
  let prophecy_module_ident ~loc typ = 
      let prophecy_mod_string = ProphPredefs.proph_mod_ident_prefix ^ Type.to_string typ in
      Ident.make loc (ProgUtils.serialize prophecy_mod_string) 0

  (* Utility function to generate fully qualified ident (qual_ident) to refer to the prophecy module. Computing the right scope to add the prophecy module. This only matters if abstract and custom types are used to create prophecy variables, otherwise the Prophecy module gets added to the root. But Raven's module system adds certain restrictions to where types and objects can and can't be defined or used. *)
  let prophecy_module_from_type_qi ~loc typ =
    (* Type.symbols returns a set of all user-defined types that are referenced in a given type. *)
    let symbols = Type.symbols typ in
    (* This turns out to be the right place to add the new module. *)
    let module_scope = ProgUtils.largest_common_prefix_qi symbols in

    (* Construct the new qual_ident, by combining `module_scope` and `prophecy_module_ident` *)
    QualIdent.append module_scope (prophecy_module_ident ~loc typ)

  (* We need to return the list of fields that this command depends on. Since we model prophecy resources using a field defined in `prophecyLib.rav`, that field gets updated. The qual_ident for this is built by combining  *)
  let stmt_ext_fields_accessed stmt_ext exprs = 
    match stmt_ext, exprs with
    | NewProph (_, typ), _ ->
      let proph_mod_qi = prophecy_module_from_type_qi ~loc:Loc.dummy typ in
      let proph_field_ident = ProphPredefs.field_ident in

      (* Append the fixed proph_field_ident (specified in prophecyLib.rav), to the specific instantiation of the prophecy module.  *)
      [QualIdent.append proph_mod_qi proph_field_ident]

      (* Same field getting modified when resolvin a prophecy. *)
    | ResolveProph, [proph_id; resolve_val] ->
      let typ = Expr.to_type resolve_val in
      let proph_mod_qi = prophecy_module_from_type_qi ~loc:Loc.dummy typ in
      let proph_field_ident = ProphPredefs.field_ident in

      [QualIdent.append proph_mod_qi proph_field_ident]

    | ResolveProph, _ ->
      Error.internal_error Loc.dummy "[EXT] ProphecyExt: wrong number of arguments called for ResolveProph"

    | _ -> Cont.stmt_ext_fields_accessed stmt_ext exprs


  (* Rewriter *)

  (* These methods are used if our constructors contain _type_expr_'s. They will mostly directly be copied from `Cont`.
    
    In this rare case, the NewProph constructor contains a type expression. 
    
    ~f refers to a function which *rewrites* types. This is part of Raven's internal infrastructure of rewrites.
  *)
  let expr_ext_rewrite_types = Cont.expr_ext_rewrite_types
  let stmt_ext_rewrite_types ~f stmt_ext = 
    let open Rewriter.Syntax in
    match stmt_ext with
    | NewProph (b, tp_expr) ->
      (* We run `f` on the type_expr we contain, and re-build the stmt_ext constr. *)
      let+ tp_expr = f tp_expr in
      NewProph (b, tp_expr)
    |_ -> Cont.stmt_ext_rewrite_types ~f stmt_ext


  (* Typing *)

  (* Perform type-checking on type_expr. The underlying type is stored in the AST as follows:
    Type.App (TypeExt type_ext, type_args, type_attr)
    
    type_check_type_expr_functs contains functions from `Typing.ml` useful for type-checking. These are defined in ExtApi.ml.
  *)
  let type_check_type_expr type_ext type_args type_attr type_check_type_expr_functs = 
    match type_ext, type_args with
    | ProphId, [] ->
      (* Not much type-checking needed. As long as no arguments are given, it is a valid type_expr. Making sure to set Type.ghost. *)
      Rewriter.return @@  (Type.App (TypeExt ProphId, [], type_attr) |> Type.set_ghost true)
      
    | ProphId, _ ->
      (* Raise type_error otherwise. *)
      Error.type_error type_attr.Type.type_loc "[EXT] ProphecyExt: wrong number of arguments used with ProphId type"

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
    | ProphResource, [proph_id_expr; value_expr] ->
      (* Generating the `Proph` type_expr with the right location. *)
      let proph_id_type = proph_id_type ~loc:expr_attr.expr_loc in

      (* Type-checking proph_id_expr *)
      (* Using `proph_id_type` as expected_type *)
      let* proph_id_expr = type_check_expr_functs.process_expr proph_id_expr proph_id_type in

      (* Type-checking value_expr *)
      let* value_expr = type_check_expr_functs.process_expr
      (* Using `Type.any` as expected type--but with `ghost` attribute set to true. *)
      value_expr (Type.any |> Type.set_ghost true) in

      (* value_expr is expected to have a `List[Type]` type. 
        Cont.ListFns.list_tp_to_elem_typ is an API call to extract `Type` from `List[Type]`.

        It returns an `type_expr option`, so it returns None if the input is not a `List[.]` type.

        The reason this is being called from Cont, is because List is also another extension. This means that its constructors are not available when compiling this extension.
      *)
      let elem_tp_opt = Cont.ListFns.list_tp_to_elem_typ (Expr.to_type value_expr) in

      begin match elem_tp_opt with
      (* A `List[.]` type NOT found. That's a type_error. *)
      | None -> Error.type_error loc 
          ("[EXT] ProphecyExt: prophecy() expected to be called with List types; found: " ^ (Type.to_string (Expr.to_type value_expr)))
      (* Okay, everything checks out. Type-checking successful. Reconstruct the expression, with the right type (Type.perm, for "permissions" represents the type_expr for resources ) *)
      | Some _elem_typ ->
        Rewriter.return @@ (Expr.mk_app ~loc ~typ:Type.perm (ExprExt ProphResource) [proph_id_expr; value_expr]) 
      end
    
    (* Incorrect number of arguments found; raise a type_error. *)
    | ProphResource, _ ->
      Error.type_error loc "[EXT] ProphecyExt: prophecy() called with incorrect number of arguments"

    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ type_check_expr_functs


  (* Type-checking of stmts. The underlying stmt in the AST is represented as:
      Stmt.{ 
        stmt_desc = Basic (StmtExt (stmt_ext, expr_list)); 
        stmt_loc = stmt_loc; 
      }
    
    `disam_tbl` is a data structure used to disambiguate local variables occuring in different subscopes by assigning a unique `ident_num` to each local variable. There is no need to understand how this works or to manipulate this manually. Some functions require and return this argument, which indicates how this must be used. However, care must be made to update and return this correctly.

    This function returns a `Stmt.basic_stmt_desc`. This is an object like:
      (StmtExt (stmt_ext, expr_list))
    In addition, a `disam_tbl` must be returned.
    `type_check_stmt_functs` is again a set of functions from `typing.ml` that are useful for type-checking statements.
  *)
  let type_check_stmt call_decl (stmt_ext : Stmt.stmt_ext) (expr_list: expr list) (stmt_loc: Loc.t) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : ExtApi.type_check_stmt_functs)
  :
      (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t = 

    (* A Raven debug statement. *)
    Logs.debug (fun m -> m "[EXT] ProphecyExt.type_check_stmt: started");
    
    let open Rewriter.Syntax in
    (* Determining whether we are in a ghost scope. Certain actions aren't allowed in ghost scopes, such as making concrete program steps, procedure calls, etc. *)
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    match stmt_ext, expr_list with
      (* ```proph_id, proph_val := Proph.new[typ]``` *)
    | NewProph (oneshot_b, typ), [proph_id; proph_val] ->
      (* Type-check `proph_id`. From `type_check_stmt`, we must call `disambiguate_process_expr, instead of `process_expr` to make sure we use `disam_tbl` consistently.  *)
      let* proph_id = type_check_stmt_functs.disambiguate_process_expr proph_id (proph_id_type ~loc:stmt_loc) disam_tbl
      
      in

      let proph_val_typ = if oneshot_b then
        (* If it is a one-shot prophecy, the type for `proph_val` is same as the type annotation on `Proph.new_1[.]`, ie `typ` *)
        typ |> Type.set_ghost true
      else
        (* Else, the type for `proph_val` is `List[typ]`. We use `Cont.ListFns.mk_list_tp` to construct this List type. *)
        Cont.ListFns.mk_list_tp stmt_loc typ |> Type.set_ghost true
      in

      begin match Expr.is_ident proph_val with
      | false ->
        (* Must be called on a local variable; otherwise type_error. *)
        Error.type_error stmt_loc "[EXT] ProphecyExt: NewProph should only be called with a local variable for value."
      
      | true ->
        (* Type-checking proph_val. *)
        let* proph_val = type_check_stmt_functs.disambiguate_process_expr proph_val proph_val_typ disam_tbl in

        (* Everything checks out. Constructing final `Stmt.basic_stmt_desc` to return.
          Making sure to use updated and type-checked values `proph_id` and `proph_val`. not stale values.
        *)
        (Stmt.StmtExt (
          NewProph (oneshot_b, typ), [proph_id; proph_val]
        ), disam_tbl) |> Rewriter.return
      end
    | NewProph _, _ ->
      Error.type_error stmt_loc "[EXT] ProphecyExt: NewProph called with incorrect number of arguments"

      (* ```Proph.resolve(proph_id, resolve_value)``` *)
    | ResolveProph, [proph_id; resolve_value] ->
      (* Type-checking arguments *)
      let* proph_id = type_check_stmt_functs.disambiguate_process_expr proph_id (proph_id_type ~loc:stmt_loc) disam_tbl in

      let* resolve_value = type_check_stmt_functs.disambiguate_process_expr resolve_value (Type.any |> Type.set_ghost true) disam_tbl in

      (* Constructing final return `Stmt.basic_stmt_desc` *)
      (Stmt.StmtExt (
        ResolveProph, [proph_id; resolve_value]
      ), disam_tbl) |> Rewriter.return

    | ResolveProph, _ ->
      Error.type_error stmt_loc "[EXT] ProphecyExt: ResolveProph called with incorrect number of arguments"

    | _ -> Cont.type_check_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl type_check_stmt_functs


  (* Rewrites *)

  (** Safely initialize prophecy module and return its qual_ident. In particular, this function is idempotent, so can be called whenever need to convert a type_expr into its corresponding prophecy_module_qual_ident. 
  
  This function is used to take any type_expr, check if a Prophecy module has been instantiated for this type, and if not, then define and instantiate such a Prophecy module for that type.
  
  *)
  let initialize_prophecy_module loc (typ: type_expr): qual_ident Rewriter.t =
    let open Rewriter.Syntax in

    (* This is the canonical qual_ident that a type's prophecy_module must be at. *)
    let proph_module_qi = prophecy_module_from_type_qi ~loc typ 
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
      (* Proph Module not found. Initializing... *)

      (* `proph_module_insert_scope`, and `proph_module_reference_scope` refer to two different scope. 
        - The first is the location where the instantiation of `Library.Prophecy` module must be inserted.  
        - The second is part of the fully qualified ident from which to reference the aforementioned `Library.Prophecy` module.

        The reason these might be different, is if we have for instance:
          ```raven

            interface A
            module F[C: A] { type T = ...; }
            module A0 : A
            module M = F[A0]

             ...Proph.new[M.T]; ...
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
          Error.internal_error loc "[EXT ProphecyExt: largest_prefix scope not found"
        | Some (qi, (name, symbol, _)) ->
          (* This returns an internal symbol_tbl object. This includes a potential renaming map, which is not too important. *)
          Rewriter.return (name, qi)
        end
      in

      (* We generate a module satisfying the `Library.Type` interface, with the right `List[.]` type. *)
      let* type_module_qi = 
        (* Module must be of List[typ] *)
        let list_typ = Cont.ListFns.mk_list_tp loc typ in

        (* Similarly, a canonical qual_ident exists for the `type_module` too. *)
        let type_module_canonical_qi =
          let mod_name_string = ProgUtils.tp_mod_ident_prefix ^ Type.to_string list_typ in
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
              ProgUtils.intros_type_module ~loc ~scope:proph_module_insert_scope ~f:!(Rewriter.process_symbol_ref) list_typ in
          
          Logs.debug (fun m -> m "[EXT] ProphecyExt.initialize_prophecy_module: Type module successfully initialized. type_module_qi: %a" QualIdent.pr type_module_canonical_qi);
            type_module_canonical_qi
      in

      (* Finally, we generate the name for the final Prophecy module. *)
      let proph_module_ident = prophecy_module_ident ~loc typ in

      (* Definition of module instantiation. This is equivalent to the Raven syntax:
        ```
          proph_module_ident = ProphPredefs.proph_mod_qi [ type_module_qi ]
        ```
       *)
      let proph_module_inst = Module.ModInst {
        mod_inst_name = proph_module_ident;
        mod_inst_type = ProphPredefs.proph_mod_qi;
        mod_inst_def = Some (ProphPredefs.proph_mod_qi, [type_module_qi]);
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

    We replace any reference to `Proph` type with references (`Ref`s). This is because prophecies are modeled using resources, and in Raven only `Ref`s can have resources associated (one per field).
    
    *)
  let rewrite_type_ext (type_ext: Type.type_ext) (tp_list: type_expr list) (loc: location) : type_expr Rewriter.t =
    match type_ext, tp_list with
    | ProphId, [] ->
      Rewriter.return Type.ref
    | ProphId, _ ->
      Error.type_error loc "[EXT] ProphExt: ProphId type constructor used with incorrect number of arguments"
    | _ -> Cont.rewrite_type_ext type_ext tp_list loc


  
  (* Rewriting expressions. *)
  let rewrite_expr_ext (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr: Expr.expr_attr) = 
    let open Rewriter.Syntax in
    let loc = expr_attr.expr_loc in
    match expr_ext, expr_list with
    | ProphResource, [proph_id; value] ->
      let* proph_type = 
        (* Extracting element type from the List[.] type of `value`. *)
        let elem_tp_opt = Cont.ListFns.list_tp_to_elem_typ (Expr.to_type value) in

        match elem_tp_opt with
        (* Must be a List[.] type *)
        | None -> Error.type_error loc ("[EXT] ProphecyExt: Prophecy resources must hold List values; found: " ^ (Type.to_string (Expr.to_type value)))
        | Some elem_typ -> 
          (* We call `Typing.expand_type_expr` (via the Rewriter.expand_type_expr_ref), to make sure we get uniform, fully expanded types. *)
          let+ elem_typ = !Rewriter.expand_type_expr_ref elem_typ in
          elem_typ
      in

      (* Initialize prophecy_module if it doesn't exist. No worries if it does. *)
      let* proph_module_qi = initialize_prophecy_module loc proph_type in
      let prophecy_field_qi = QualIdent.append proph_module_qi ProphPredefs.field_ident in

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


  (* Rewriting Statements *)
  let rewrite_stmt_ext (stmt_ext: Stmt.stmt_ext) (expr_list: expr list) loc: Stmt.t Rewriter.t =
    let open Rewriter.Syntax in

    Logs.debug (fun m -> m "[EXT] ProphecyExt.rewrite_stmt: Starting");

    match stmt_ext, expr_list with
    (* ```proph_id, proph_val := Proph.new[typ]``` *)
    | NewProph (oneshot_b, typ), [proph_id; proph_val] ->

      Logs.debug (fun m -> m "[EXT] ProphecyExt.rewrite_stmt: NewProph(one_shot:%b; type:%a)" oneshot_b Type.pr typ);

      (* using `initialize_prophecy_module` to generate the proph_module_qi. *)
      let* proph_module_qi = initialize_prophecy_module loc typ in
      let prophecy_field_qi = QualIdent.append proph_module_qi ProphPredefs.field_ident in

      let* prophecy_field_symbol = Rewriter.find_and_reify_field prophecy_field_qi in

      (* Building Raven statements to encode semantics. *)
      (* ```havoc proph_id``` *)
      let havoc_stmt1 = Stmt.mk_havoc ~loc (Expr.to_qual_ident proph_id) in
      (* ```havoc proph_val``` *)
      let havoc_stmt2 = Stmt.mk_havoc ~loc (Expr.to_qual_ident proph_val) in

      (* dealing with one-shot and sequence prophecies separately. *)
      let* proph_field_val = if not oneshot_b then 
        (* nothing to do for sequence prophecies. *)
        Rewriter.return proph_val 
      else
          (* For one-shot prophecies, generating an arbitrary tail of predictions. *)
        let tl_var = Type.mk_var_decl ~const:true ~ghost:true (Ident.fresh loc "$proph_oneshot_trail") (Cont.ListFns.mk_list_tp loc (Expr.to_type proph_val)) in
        let+ tl_var_qi = Rewriter.introduce_typecheck_symbol' ~loc (
          VarDef { 
            var_decl = tl_var;
            var_init = None;
            var_is_free = false;
          }
        ) in

        (* ```proph_val :: tl_val``` *)
        Cont.ListFns.ls_cons loc (proph_val) (Expr.from_var_decl tl_var)
      in

      (* ```inhale own(proph_id, prophecy_field_qi, proph_field_val, 1.0)``` *)
      let proph_new_stmt =
        Stmt.mk_inhale_expr ~loc
        ~cmnt:("[EXT] ProphExt: Inhale stmt for Prophecy.new()")
        (Expr.mk_app ~loc ~typ:Type.perm Expr.Own [
          proph_id; 
          Expr.mk_var ~typ:prophecy_field_symbol.field_type prophecy_field_qi; 
          proph_field_val;
          Expr.mk_real 1.0;
        ])

        (* Previously using a new_stmt. Both approaches are equivalent. *)
        (* let new_desc = {
          Stmt.new_lhs = Expr.to_qual_ident proph_id;
          new_args = [(prophecy_field_qi, Some proph_field_val)]
        } in

        { Stmt.stmt_desc = Basic (New new_desc); stmt_loc = loc } *)
      in

      (* Create a block_stmt containing all the statements. This block is indeed a ghost block, so setting ~ghost:true *)
      Rewriter.return (Stmt.mk_block_stmt ~loc ~ghost:true
        [havoc_stmt1; havoc_stmt2; proph_new_stmt]
      )

    | NewProph _, _ ->
            Error.type_error loc "[EXT] ProphExt: NewProph command called with incorrect number of arguments"

    (* For ```Proph.resolve(proph_id, resolve_value)``` statements *)
    | ResolveProph, [proph_id; resolve_value] ->
      let* proph_module_qi = initialize_prophecy_module loc (Expr.to_type resolve_value) in
      let prophecy_field_qi = QualIdent.append proph_module_qi 
        (Ident.set_loc loc ProphPredefs.field_ident) 
      in

      let* prophecy_field = Rewriter.find_and_reify_field prophecy_field_qi in

      (* The type of the prophecy field will always be List[typ-of-resolve_value] *)
      let proph_list_tp = Cont.ListFns.mk_list_tp loc (Expr.to_type resolve_value) in

      (* Creating new local variable to store value of `proph_id.prophecy_field` *)
      let proph_read_var_def, proph_read_var_ident = 
        (* Ident.fresh to generate new fresh ident. *)
        let proph_read_var_ident = Ident.fresh loc "$proph_read" in
        let proph_read_type = proph_list_tp in

        (* Creating a `var_def` object, used to introduce the new local variable. *)
        Stmt.{ 
          var_decl = Type.mk_var_decl ~ghost:true proph_read_var_ident ~loc proph_read_type ; 
          var_init = None;
          var_is_free = false;
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

    | ResolveProph, _ ->
      Error.type_error loc "[EXT] ProphExt: ResolveProph command called with incorrect number of arguments"

    | _ -> Cont.rewrite_stmt_ext stmt_ext expr_list loc


  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
  let ext_local_vars = local_vars @ Cont.ext_local_vars
end
