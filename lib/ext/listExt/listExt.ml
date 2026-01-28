open Base
open Ast
open ExtApi
open Util

(** Here we implement an extension that adds support for polymorphic lists. This is a core Raven extension and is always enabled.

This extension introduces:
  - `List[T]` polymorphic List type.
  - `List.nil` and `List.cons(., .)` polymorphic constructors 
  - `List.hd()` and `List.tl()` List destructors.
  - Some library functions like `List.len()` and `List.is_in()`.
*)

module ListExt (Cont : Ext) = struct
  (* Config *)
  let lib_source = None
  let local_vars = []

  (* Defining pre-fixed idents for List functions  *)
  module ListPredefs = struct
    let list_mod_ident_prefix = "ListExtMod$$"
    let cons_ident = Ident.make Loc.dummy "cons" 0
    let nil_ident = Ident.make Loc.dummy "nil" 0

    let hd_destr_ident = Ident.make Loc.dummy "hd" 0
    let tl_destr_ident = Ident.make Loc.dummy "tl" 0
    
    let len_ident = Ident.make Loc.dummy "len" 0
    let is_in_ident = Ident.make Loc.dummy "is_in" 0
  end

  open ListPredefs

  (* Adding List as a type constructor *)
  type Type.type_ext +=
    | ListConstr

  (* Adding a single constructor for all List expressions, such as:
      List.cons, List.nil, List.hd, List.tl, etc, 
    to be distinguished by the `ident` stored in the constructor. 

    It was done this way to allow us to more easily expand our List library with new functions.
  *)
  type Expr.expr_ext +=
    | ListExpr of ident


  (* Implementing ListFns to satisfy ListApi *)
  module ListFns: ExtApi.ListFns = struct
    let listTpConstr () = ListConstr

    let mk_list_tp loc tp = Type.mk_app ~loc (TypeExt ListConstr) [tp]

    let ls_cons loc hd_expr tl_expr = 
      Expr.mk_app ~loc ~typ:(Expr.to_type tl_expr)
        (ExprExt (ListExpr ListPredefs.cons_ident))
      [hd_expr; tl_expr]

    let ls_nil loc ~elem_typ () = 
      Expr.mk_app ~loc ~typ:(mk_list_tp loc elem_typ)
        (ExprExt (ListExpr ListPredefs.nil_ident))
      []

    let ls_hd loc ls_expr = 
      let elem_type = 
        match (Expr.to_type ls_expr) with
        | Type.App (TypeExt ListConstr, [elem_tp], _) -> elem_tp
        | _ -> Error.type_error loc "[EXT] ListExt: List.hd called on a mistyped argument"
      in
      Expr.mk_app ~loc ~typ:(elem_type) 
        (ExprExt (ListExpr ListPredefs.hd_destr_ident))
      [ls_expr]

    let ls_tl loc ls_expr =
      Expr.mk_app ~loc
      ~typ:(Expr.to_type ls_expr)
      (ExprExt (ListExpr ListPredefs.tl_destr_ident))
      [ ls_expr ]

    let ls_len loc ls_expr =
      Expr.mk_app ~loc
        ~typ:(Type.int)
      (ExprExt (ListExpr ListPredefs.len_ident))
      [ls_expr]

    let mk_list_tp loc tp = Type.mk_app ~loc ~ghost:(Type.is_ghost tp) (TypeExt ListConstr) [tp]

    let list_tp_to_elem_typ tp_expr =
      match tp_expr with
      | Type.App (TypeExt ListConstr, [elem_typ], _) ->
        Some elem_typ
      | Type.App (Var list_tp_qi, [], _) -> 

        let tp_mod_ident =  (QualIdent.pop list_tp_qi).qual_base in

        if String.is_prefix tp_mod_ident.ident_name ~prefix:ListPredefs.list_mod_ident_prefix then
          
          let elem_typ_qi = (QualIdent.append (QualIdent.append (QualIdent.pop list_tp_qi) Predefs.lib_list_arg_mod_ident) Predefs.lib_type_rep_type_ident) in
          Some (
            Type.App (Var elem_typ_qi, [], Type.dummy_attr)
          )
        else
          None
      | _ -> None

  end

  (* AstDef *)
  (* Defining standard functions for AST functionality. *)
  let type_ext_to_name type_ext =
    match type_ext with 
    | ListConstr -> "List"
    | _ ->
      (* Defer to `Cont` whenever an unknown extension found. *)
      Cont.type_ext_to_name type_ext

  let expr_ext_to_string expr_ext =
    match expr_ext with 
    | ListExpr c -> "List." ^ Ident.to_string c 
    | _ -> Cont.expr_ext_to_string expr_ext

  (* No statement extension, so directly defer to `Cont`. *)
  let pr_stmt_ext ppf ext expr_list = 
    match ext, expr_list with
    | _ -> Cont.pr_stmt_ext ppf ext expr_list

  let stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | _ -> Cont.stmt_ext_symbols stmt_ext

  (* We can even define functions directly equal. *)
  let stmt_ext_local_vars_modified = Cont.stmt_ext_local_vars_modified
  
  let stmt_ext_fields_accessed = Cont.stmt_ext_fields_accessed


  (* Rewriter *)
  (* These functions are meant to be used if a `expr_ext` or `stmt_ext` constructor stores a `type_expr`, for example `ProphecyExt`. In most extensions, these are deferred to `Cont`. *)
  let expr_ext_rewrite_types = Cont.expr_ext_rewrite_types
  let stmt_ext_rewrite_types = Cont.stmt_ext_rewrite_types


  (* Typing *)
  (** Now we come to the fun stuff. Type-checking of type_expr. The underlying type is stored in the AST as follows:
    Type.App (TypeExt type_ext, type_args, type_attr)

  This function is used in `Typing.ProcessTypeExpr.process_type_expr`, to type-check extension types.
  *)
  let type_check_type_expr (type_ext: Type.type_ext) (type_args: type_expr list) (type_attr: Type.type_attr) (type_check_type_expr_functs: type_check_type_expr_functs) =
    (* Rewriter.Syntax lets us use `Rewriter` monadic bindings like `let*` and `let+`. *)
    let open Rewriter.Syntax in
    match type_ext, type_args with
    | ListConstr, [elem_typ] ->
      (* If it is our extension, make sure the arguments and type_expr are sound. *)

      (* Recursively call `process_type_expr` on the member type. 
      Note that we use the `Rewriter` monadic binding `let*` to call `process_type_expr`. This monad threads the symbol table through the program, and binds the return values, without having to explicitly handle it. 
      
      We are able to do this because `type_check_type_expr` has a return type of `type_expr Rewriter.t`. This lets us use any state-dependent functions from Raven's library.
      *)
      let* elem_typ = type_check_type_expr_functs.process_type_expr elem_typ in

      (* Construct the new `type_expr`. Using `Type.mk_app` library function from `AstDef`. 
      `Type.set_ghost_to tp1 tp2` sets the `ghost` attribute of `tp2` to `tp1`, so this ensures it carries over.
      Types have a _ghost_ attribute which tracks whether a type is being used in a ghost setting or a non-ghost setting. "Ghost" here refers to whether the given statement corresponds to the concrete program ("non-ghost"), or the proof ("ghost"). There are respective constraints on what one is and is not allowed to do in setting. 
      
      For example: ghost state cannot be used in non-ghost setting, to prevent the mixing of the program and the proofs. Similarly, in ghost setting, procedure calls cannot be made, because those calls might have observable effects and ghost settings are only for manipulating "ghost" or logical resources.

      Finally, one must apply `Rewriter.return` to this function to convert the `type_expr` from a plain value to a monadic value of the `Rewriter` monad. Another possibility is to change the `let*` above to `let+`, and omit the call to `Rewriter.return`. These are equivalent.
      *)
      (Type.mk_app ~loc:type_attr.type_loc (TypeExt ListConstr) [elem_typ]) |> Type.set_ghost_to elem_typ |> Rewriter.return 

    | ListConstr, _ ->
      (* If incorrect number of arguments are given, throw a type_error.
        lib/util/error.ml provides error-handling. `Error.type_error` takes a _loc_ argument. This _loc_ refers to a location in the source text stream. This is used to locate errors for the user. Most Raven objects carry location data with them in one form or another.
      *)
      Error.type_error type_attr.type_loc "[ListExt] List type called with incorrect number of arguments"

      (* Otherwise defer to `Cont`. *)
    | _ -> Cont.type_check_type_expr type_ext type_args type_attr type_check_type_expr_functs

  (* Type-checking of expressions. This takes an additional `expected_typ` argument which carries typing information from the surrounding. This is often `Type.any`, the most general typing annotation. *)
  let type_check_expr (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr : Expr.expr_attr) (expected_typ: type_expr) (type_check_expr_functs: type_check_expr_functs) = 
    let open Rewriter.Syntax in
    
    match expr_ext, expr_list with
    | ListExpr c, exprs -> begin
      (* Our first debugging statement! Debugging statements appear when one runs `raven` with the `-v -v` flag. Be careful though, Raven spits out a _lot_ of debug statements.
      
      Usually debug statements print current location as well as values of some relevant variables. Each (most!) type in Raven have a corresponding printer function, which is used to print `ident` and `expr list`. 
      *)
      Logs.debug (fun m -> m "[EXT] ListExt.type_check_expr: List.%a; args= %a; expected_is_ghost=%b" Ident.pr c (Util.Print.pr_list_comma Expr.pr) expr_list (Type.is_ghost expected_typ));

      (* Propagating "ghost" attribute to sub-expressions. *)
      let expr_list = List.map expr_list ~f:(fun expr ->
        let ghost_status = Type.is_ghost expected_typ || (Type.is_ghost (Expr.to_type expr)) in

        Expr.set_type expr ((Expr.to_type expr) |> Type.set_ghost ghost_status)
      )
      in

      (* Recursively type-checking sub-expressions with `process_expr`. We use `let*` and `Rewriter.List.map` because we want to use the Rewriter monad in the function `f`. This is because `process_expr` needs to symbol_tbl to be able to type_check expressions, thus it has a return type of `expr Rewriter.t`. *)
      let* expr_list = Rewriter.List.map  expr_list ~f:(fun expr -> type_check_expr_functs.process_expr expr (Expr.to_type expr)) in

      (* Propagating "ghost" attribute from sub-expressions main expression. *)
      let is_ghost = List.fold ~init:false (expected_typ :: List.map exprs ~f:Expr.to_type) 
        ~f:(fun accum tp -> 
        accum || Type.is_ghost tp 
      )
      in

      (* `c` is the `ident` stored in the `ListExpr` constructor. `c` determines what List operation it is. We first deal with the two constructors, `cons` and `nil`. *)
      match c, exprs with
      | ident, [ls_head; ls_tail] when Ident.(ident = cons_ident)  ->
        (* Using the `when` guard to restrict `ident` to `cons_ident` *)

        (* `expand_type_expr` is a best-practice for type_expr's while type-checking. It recursively looks up and inlines type definitions pointing to other type_expr. We also propagate `ghost` attribute. *)
        let* expected_typ = type_check_expr_functs.expand_type_expr expected_typ in
        let expected_typ = expected_typ |> Type.set_ghost is_ghost in
        let elem_type = match expected_typ with
          (* if `expected_typ` already contained the type of the list, we just use that. *)
          | App (TypeExt ListConstr, [elem_typ], _) -> (elem_typ |> Type.set_ghost_to expected_typ)
          (* else we set elem_type to Type.any. *)
          | App (Any, [], _) -> Type.any |> Type.set_ghost_to expected_typ
          (* otherwise this is a type-error *)
          | _typ -> 
            (* type_mismatch_error takes as arguments the "expected" type and the "discovered" type.
            
            (Type.App (TypeExt ListConstr, [Type.any], Type.mk_attr (expr_attr.expr_loc)))

            refers to the `List[Any]` type.
            *)
              type_check_expr_functs.type_mismatch_error expr_attr.expr_loc (Type.App (TypeExt ListConstr, [Type.any], Type.mk_attr (expr_attr.expr_loc)))  _typ
        in
        (* Logs.debug (fun m -> m "[EXT] ListExt.type_check_expr: elem_typ=%a; is_ghost=%b; ls_head = %a" Type.pr elem_type (Type.is_ghost elem_type) Expr.pr ls_head); *)
        (* process the `ls_head` expression *)
        let* ls_head = type_check_expr_functs.process_expr ls_head elem_type in
         (* inferring back the type from `ls_head` after type-checking.  *)
        let elem_type = (Expr.to_type ls_head) in

        (* constructing the `List` type_expr, to type-checking `ls_tail`. *)
        let list_type = (Type.App (TypeExt ListConstr, [elem_type], Type.mk_attr (expr_attr.expr_loc))) |> Type.set_ghost_to expected_typ in

        (* Type-checking the `ls_tail` expression, with `list_type` as its expected type. *)
        let* ls_tail = type_check_expr_functs.process_expr ls_tail list_type in
        let list_type = list_type |> Type.set_ghost (Type.is_ghost (Expr.to_type ls_head) || Type.is_ghost (Expr.to_type ls_tail)) in

        (* Finally, using the `check_and_set` function to return the final expression, with the type-checked sub-expressions. 
      
        `check_and_set` takes as arguments the type lowerbound, type upperbound and expected type for the given expression.
        *)
        type_check_expr_functs.check_and_set
        (App (ExprExt (ListExpr cons_ident), [ls_head; ls_tail], expr_attr)) list_type list_type list_type

      | ident, _ when Ident.(c = cons_ident)  ->
        (* if it is a `List.cons` expression with a different number of arguments, raise a type_error. *)
        Error.type_error expr_attr.expr_loc "Incorrect number of arguments for List Cons expression"

      | ident, [] when Ident.(ident = nil_ident) ->
        (* `List.nil` *)
        Logs.debug (fun m -> m "[Ext] ListExt.type_check_expr: typechecking nil");

        let elem_type = match expected_typ with
        (* if `expected_typ` contains the final type, then we set the type accordingly. *)
        | App (TypeExt ListConstr, [elem_typ], _) -> elem_typ |> Type.set_ghost is_ghost
        (* if `expected_typ` is `Type.any`, then we set to the `Type.bot` (bottom) type. This is because in this case, we have no information about the element type. *)
        | App (Any, [], _) -> Type.bot
        | _typ -> type_check_expr_functs.type_mismatch_error expr_attr.expr_loc (Type.App (TypeExt ListConstr, [Type.any], Type.mk_attr (expr_attr.expr_loc)))  _typ
        in

        (* Construct the list type_expr: `List[elem_type]` *)
        let list_type = (Type.App (TypeExt ListConstr, [elem_type], Type.mk_attr (expr_attr.expr_loc))) in
        
        (* `check_and_set` the final expression type. *)
        type_check_expr_functs.check_and_set
        (App (ExprExt (ListExpr nil_ident), [], expr_attr)) list_type list_type list_type

      | ident, _ when Ident.(ident = nil_ident) ->
        Error.type_error expr_attr.expr_loc "Incorrect number of arguments for List.nil expression"

      | ident, [] ->
        (* the assumption is that all `List` library arguments will take the list as the first arguement. Thus, if no arguments, that's an error. *)
        Error.internal_error expr_attr.expr_loc ("[EXT] ListExt.type_check_expr: Unknown list function called: " ^ (Ident.to_string ident))

      | ident, ls_expr :: args ->
        (* assume first expr is the list expression *)

        (* This returns the actual in-memory representation of the `Library.ListM` module, defined in `lib/library/base_types.ml` *)
        let* lib_list_module = Rewriter.find_and_reify_module Predefs.lib_list_mod_qual_ident in

        (* We check to see if the `List` function exists in this module. 
          `lib_list_module.mod_def` contains a list of all symbols defined in the module. We use `Symbol.to_name` to convert symbols to names, and compare idents. *)
        let does_elem_exist = List.find lib_list_module.mod_def ~f:(fun mem -> 
          match mem with 
          | Import _ -> false 
          | SymbolDef symbol -> Ident.(Symbol.to_name symbol.symbol_def = ident) 
        ) in
      
        match does_elem_exist with
        (* callable does not exist inside Library.ListM *)
        | None | Some Import _->
          (* Generate an error if function not found *)
          Error.internal_error expr_attr.expr_loc ("[EXT] ListExt: Unknown list function called: " ^ (Ident.to_string ident))

        (* found callable inside Library.ListM *)
        | Some SymbolDef symbol ->
          (* type-check the `ls_expr` first. We set `Type.any` as the expected type, since we have no information. *)
          let* ls_expr = type_check_expr_functs.process_expr ls_expr (Type.any |> Type.set_ghost is_ghost) in

          (* extract `elem_type` from the type-checked `ls_expr` *)
          let elem_type = match (Expr.to_type ls_expr) with
          | App (TypeExt ListConstr, [elem_typ], _) -> 
              elem_typ |> Type.set_ghost (is_ghost || Type.is_ghost elem_typ)
          | _tp -> 
            (* if not `List` type, throw a type-error. *)
            let list_type = (Type.App (TypeExt ListConstr, [Type.any], Type.mk_attr (expr_attr.expr_loc))) in
            type_check_expr_functs.type_mismatch_error expr_attr.expr_loc list_type _tp
          in

          let is_ghost = is_ghost || Type.is_ghost elem_type in

          let list_type = (Type.App (TypeExt ListConstr, [elem_type], Type.mk_attr (expr_attr.expr_loc))) |> Type.set_ghost is_ghost in

          (* type-checking all remaining function arguments. *)
          let* args = Rewriter.List.map args ~f:(fun arg -> 
            type_check_expr_functs.process_expr arg 
              (Type.any |> Type.set_ghost is_ghost)
          ) in

          if Ident.(ident = len_ident) then
            (* `List.len()` *)
            let expected_typ = Type.int |> Type.set_ghost is_ghost in
            match args with
            | [] -> type_check_expr_functs.check_and_set (Expr.App (ExprExt (ListExpr ident), [ls_expr], expr_attr)) expected_typ expected_typ expected_typ
            | _ -> 
              (* type-error *)
              Error.type_error expr_attr.expr_loc "[EXT] ListExt: List.len called with incorrect number of arguments"
          else if Ident.(ident = is_in_ident) then
            (* `List.is_in()` *)
            let expected_typ = Type.bool |> Type.set_ghost is_ghost in
            match args with
            | [elem_arg] ->
              if Type.(elem_type = Expr.to_type elem_arg) then
                (* if type of element matches `elem_type` *)
                type_check_expr_functs.check_and_set (Expr.App (ExprExt (ListExpr ident), ls_expr :: args, expr_attr)) expected_typ expected_typ expected_typ
              else 
                (* else, type error *)
                type_check_expr_functs.type_mismatch_error (Expr.to_loc elem_arg) elem_type (Expr.to_type elem_arg)
            | _ -> Error.type_error expr_attr.expr_loc "[EXT] ListExt: List.is_in called with incorrect number of arguments"
          else if Ident.(ident = hd_destr_ident) then
            (* `List.hd` *)
            match args with
            | [] -> 
              type_check_expr_functs.check_and_set (Expr.App (ExprExt (ListExpr ident), [ls_expr], expr_attr)) elem_type elem_type elem_type

            | _ -> Error.type_error expr_attr.expr_loc "[EXT] ListExt: List.hd called with incorrect number of arguments"
          else if Ident.(ident = tl_destr_ident) then
            (* `List.tl` *)
            match args with 
            | [] ->
              type_check_expr_functs.check_and_set (Expr.App (ExprExt (ListExpr ident), [ls_expr], expr_attr)) list_type list_type list_type
            | _ -> Error.type_error expr_attr.expr_loc "[EXT] List.tl called with incorrect number of arguments"
          else
            Error.internal_error expr_attr.expr_loc ("[EXT] ListExt.type_check_expr: Unknown list function called: " ^ (Ident.to_string ident))
      end

    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ type_check_expr_functs

  let type_check_stmt = Cont.type_check_stmt

  (* Rewrites *)
  let rewrite_type_ext (type_ext: Type.type_ext) (tp_list: type_expr list) (loc: location) =
    let open Rewriter.Syntax in
    match type_ext, tp_list with
    | ListConstr, [elem_typ] -> 
      (* This is where the magic happens. We rewrite the new constructors into existing Raven expressions.
      
      What happens is that for the given elem_typ, we instantiate the `Library.ListM` module with it, and replace any `ListConstr` type_expr with the name of this module.

      We make sure this module is canonical and uniquely generated, so that all reference to the same type get rewritten into the same type_expr.
      *)
      
      (* This has to do with Raven's higher-order module system. We're computing where to insert the list module and what to call it. *)
      let* list_module_insert_scope, list_module_reference_scope =
        (* In case of elem_typ being in an instantiated module, like so:
          `module M = N[P]; type T' = List[M.T]` 
        we need to insert the elem_typ Type Module in the original interface `N`, and refer to it using `M` *)
      
        let largest_prefix = ProgUtils.largest_common_prefix_qi (Type.symbols elem_typ) in
        let+ result = Rewriter.resolve_and_find_opt largest_prefix in
        match result with
        | None -> 
          Error.internal_error Loc.dummy "[EXT] ListExt: rewrite_type_ext: largest_prefix scope not found"
        | Some (qi, (name, symbol, _)) ->
          name, qi
      in

      (* always good to print some state from time to time! *)
      Logs.debug (fun m -> m "[EXT] ListExt.rewriter_type_ext: Elem_typ=%a; list_module_insert_scope=%a; list_module_reference_scope=%a" Type.pr elem_typ QualIdent.pr list_module_insert_scope QualIdent.pr list_module_reference_scope);

      (* we first introduce a Type module implementing the `Library.Type` interface. This is essentially wrapping the type_expr into a module to use as a higher order module argument.  *)
      let* type_module_qi = 
        let type_module_canonical_qi = 
          (* add a consisten prefix to these Type modules. This functionality is taken from  *)
          let mod_name_string = ProgUtils.tp_mod_ident_prefix ^ Type.to_string elem_typ in
          let type_module_ident = Ident.make loc (ProgUtils.serialize mod_name_string) 0 in
          QualIdent.append list_module_reference_scope type_module_ident
        in

        (* check if it already exists *)
        let* resolve_result = 
          Rewriter.resolve_opt type_module_canonical_qi in
        
        match resolve_result with
        | Some _ ->
          (* if so, then we're done, we can return *)
          Rewriter.return type_module_canonical_qi
        | None ->
          (* else, we introduce the type module. Fortunately, this functionality is implemented in `ProgUtils`. It takes an optional `scope` argument indicating the scope of where to introduce the type_module. *)
          let+ _ = 
            ProgUtils.intros_type_module ~loc ~scope:list_module_insert_scope ~f:!(Rewriter.process_symbol_ref) elem_typ in
          type_module_canonical_qi
      in 

      Logs.debug (fun m -> m "[EXT] ListExt.rewriter_type_ext: type_module_qi=%a" QualIdent.pr type_module_qi);

      (* creating ident for list_module *)
      let list_module_ident = 
        let mod_name_string = ListPredefs.list_mod_ident_prefix ^ Type.to_string elem_typ in
        Ident.make loc (ProgUtils.serialize mod_name_string) 0
      in

      (* preparing the Module Instantiation symbol definition *)
      let list_module_inst = Module.ModInst {
            mod_inst_name = list_module_ident;
            mod_inst_type = Predefs.lib_list_mod_qual_ident;
            mod_inst_def = Some (Predefs.lib_list_mod_qual_ident, [type_module_qi]);
            mod_inst_is_interface = false;
            mod_inst_loc = loc;
      } in

      let* list_module_inst_qi = 
        let module_qi = QualIdent.append list_module_reference_scope list_module_ident in

        (* next we check for the List module. *)
        let* resolve_result = Rewriter.resolve_opt module_qi in
        match resolve_result with
          | Some _ -> 
            (* if it exists, no need to do anything *)
            Rewriter.return module_qi
          | None ->
            let+ _ = 
              (* else we introduce this symbol using `Rewriter.introduce_typecheck_symbol_at_scope'`. This function allows one to introduce a new Raven symbol at an arbitrary scope. It also makes sure to type-check the symbol before adding.
              
              It is recommended to use either `Rewrite.introduce_typecheck_symbol'` if adding a symbol to the current scope, or this function to introduce new symbols to the AST.
              *)
            Rewriter.introduce_typecheck_symbol_at_scope' ~loc list_module_inst list_module_insert_scope in
            module_qi
      in

      Logs.debug (fun m -> m "[EXT] ListExt.rewriter_type_ext: list_module_inst_qi=%a" QualIdent.pr list_module_inst_qi);

      (* Make a var type pointing to the newly introduced list module's rep type. *)
      Rewriter.return (Type.mk_var ~loc (QualIdent.append list_module_inst_qi Predefs.lib_type_rep_type_ident))

    | ListConstr, _ ->
      Error.type_error loc "[EXT] ListExt: List type used with unexpected number of arguments"

    | _ -> Cont.rewrite_type_ext type_ext tp_list loc

  (** this function describes how to rewrite the newly introduced expressions into native Raven constructs. The expression being rewritten here is:
    Expr.App (ExprExt expr_ext, expr_list, expr_attr)
  *)
  let rewrite_expr_ext (expr_ext: Expr.expr_ext) (expr_list: expr list) (expr_attr: Expr.expr_attr) = 
    (* let open Rewriter.Syntax in *)
    let loc = expr_attr.expr_loc in

    match expr_ext, expr_list with
    | ListExpr ident, [hd; tail] when Ident.(ident = cons_ident) ->
      (* when `List.cons` *)
      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: List.cons");
      (* get List module name from type. Here, we can assume that the type rewriting has happened already, and so the list expression's type must point to a List module, and won't be `TypeExt ListConstr`. *)
      let module_name = begin match expr_attr.expr_type with
      | Type.App (Var tp_qid, [], _) ->
        QualIdent.pop tp_qid
      | _ ->
        Error.internal_error loc "[EXT] ListExt.rewrite_expr_ext crashed1; expected List Module name type"
      end 
      in

      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: expr_typ = %a" Type.pr expr_attr.expr_type);

      (* Generating the qual_ident for the `cons` constructor, by appending "cons" to the List module name. *)
      let constr_qid = QualIdent.append module_name Predefs.lib_list_cons_ident in

      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: constr_qid = %a" QualIdent.pr constr_qid);
      
      (* Finally returning a DataConstr expression. DataConstr expressions are stored under a separate constructor in Raven. *)
      Expr.mk_app ~loc ~typ:expr_attr.expr_type (DataConstr constr_qid) [hd; tail] |> Rewriter.return

    | ListExpr ident, [] when Ident.(ident = nil_ident)  ->
      (* `List.nil` *)
      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: List.nil");
      let module_name = begin match expr_attr.expr_type with
      | Type.App (Var tp_qid, [], _) ->
        QualIdent.pop tp_qid
      | _tp ->
        Error.internal_error loc ("[EXT] ListExt.rewrite_expr_ext crashed2; expected List Module name type; got " ^ (Type.to_string _tp))
      end 
      in

      (* Generating the qual_ident *)
      let constr_qid = QualIdent.append module_name Predefs.lib_list_nil_ident in
      
      (* Returning the final DataConstr expression. *)
      Expr.mk_app ~loc ~typ:expr_attr.expr_type (DataConstr constr_qid) [] |> Rewriter.return
    
    | ListExpr ident, [ls_arg] when Ident.(ident = hd_destr_ident) ->
      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: List.hd");
      let module_name = begin match Expr.to_type ls_arg with
      | Type.App (Var tp_qid, [], _) ->
        QualIdent.pop tp_qid
      | _ ->
        Error.internal_error loc "[EXT] ListExt.rewrite_expr_ext crashed3; expected List Module name type"
      end 
      in

      let constr_qid = QualIdent.append module_name Predefs.lib_list_head_destr_ident in

      (* DataDestr are also stored with a different constructor. *)
      Expr.mk_app ~loc ~typ:expr_attr.expr_type (DataDestr constr_qid) [ls_arg] |> Rewriter.return

    | ListExpr ident, [ls_arg] when Ident.(ident = tl_destr_ident) ->
      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: List.tl");
      let module_name = begin match Expr.to_type ls_arg with
      | Type.App (Var tp_qid, [], _) ->
        QualIdent.pop tp_qid
      | _ ->
        Error.internal_error loc "[EXT] ListExt.rewrite_expr_ext crashed4; expected List Module name type"
      end 
      in

      let constr_qid = QualIdent.append module_name Predefs.lib_list_tail_destr_ident in
      
      Expr.mk_app ~loc ~typ:expr_attr.expr_type (DataDestr constr_qid) [ls_arg] |> Rewriter.return

    | ListExpr ident, ls_arg :: args ->
      Logs.debug (fun m -> m "[EXT] ListExt.rewrite_expr_ext: %a" Ident.pr ident);

      (* otherwise, assume it must be a callable. *)
      let module_name = begin match (Expr.to_type ls_arg) with
      | Type.App (Var tp_qid, [], _) ->
        QualIdent.pop tp_qid
      | _ ->
        Logs.debug (fun m -> m "expr_type: %a" Type.pr expr_attr.expr_type);
        Error.internal_error loc "[EXT] ListExt.rewrite_expr_ext crashed; expected List Module name type"
      end
      in

      let call_qid = QualIdent.append module_name ident in
      
      (* Generate the function call expression. Function call expressions in Raven are represented as a Var expr with arguments. *)
      Expr.mk_app ~loc ~typ:expr_attr.expr_type (Var call_qid) (ls_arg :: args) |> Rewriter.return
    
    
    | ListExpr ident, [] ->
      Error.type_error loc "[EXT] ListExt.rewrite_expr_ext: Unknown ident." 

    | _ -> Cont.rewrite_expr_ext expr_ext expr_list expr_attr

  let rewrite_stmt_ext = Cont.rewrite_stmt_ext


  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
  let ext_local_vars = local_vars @ Cont.ext_local_vars
end
