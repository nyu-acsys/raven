(** Type checking of modules and their type, field and value members. *)

open Base
open Ast
open Util
open TypingMonad
open TypingErrors

(** Whether [typ] compiles to a single machine word: a base type (Int, Bool, Ref), or a
    data type small enough to carry a tag alongside one -- at most four constructors, each
    taking at most one base-type argument. Two bits for the tag and the remaining
    sixty-two for the value.

    Kept as a front-end check rather than a declared interface member because there is
    nothing an interface could declare that would say it. See its one caller, the
    [Library.WordSized] check in [process_module]. *)
let is_type_word_sized (typ : type_expr) : bool t =
  let open Rewriter.Syntax in
  let* typ = TypeExpr.expand_type_expr typ in
  match typ with
  | _ when Type.is_base_type typ -> Rewriter.return true
  | App (Var qual_ident, [], _) -> (
      let* _, symbol = Rewriter.resolve_and_find qual_ident in
      let+ type_def = Rewriter.Symbol.reify_type_def (Type.to_loc typ) symbol in
      match type_def with
      | Some (App (Data (_, variant_decls), [], _)) ->
          List.length variant_decls <= 4
          && List.for_all variant_decls ~f:(fun variant_decl ->
              match variant_decl.variant_args with
              | [] -> true
              | [ arg ] -> Type.is_base_type arg.var_type
              | _ -> false)
      | _ -> false)
  | _ -> Rewriter.return false

let process_type_def (type_def : Module.type_def) : Module.symbol t =
  let open Rewriter.Syntax in
  Logs.debug (fun m ->
      m "Typing.process_type_def: Start processing type_def: %a" Ident.pr
        type_def.type_def_name);
  match type_def.type_def_expr with
  | None -> Rewriter.return Module.(TypeDef type_def)
  | Some tp_expr ->
      let+ tp_expr =
        match tp_expr with
        | App (Data (_, variant_decl_list), [], _tp_attr) ->
            let* fully_qualified_tp_name =
              Rewriter.resolve (QualIdent.from_ident type_def.type_def_name)
            in

            let _ =
              if List.is_empty variant_decl_list then
                Error.error (Type.to_loc tp_expr)
                  "data types must have at least one constructor"
            in

            (* _constr_map is constructed just to make sure no duplicate constructors are used in data type declaration. *)
            let _constr_map =
              List.fold variant_decl_list
                ~init:(Map.empty (module Ident))
                ~f:(fun mp variant_decl ->
                  List.fold variant_decl.variant_args ~init:mp ~f:(fun mp var_arg ->
                      match Map.add mp ~key:var_arg.var_name ~data:var_arg with
                      | `Ok mp -> mp
                      | `Duplicate ->
                          Error.error (Ident.to_loc var_arg.var_name)
                          @@ Printf.sprintf "Duplicate constructor found in data type %s"
                               (Type.to_string tp_expr)))
            in

            let* variant_decl_list =
              Rewriter.List.map variant_decl_list ~f:(fun variant_decl ->
                  let+ variant_args =
                    Rewriter.List.map variant_decl.variant_args ~f:(fun var_decl ->
                        TypeExpr.process_var_decl var_decl)
                  in
                  { variant_decl with variant_args })
            in

            let* fully_qualified_tp_name =
              Rewriter.resolve (QualIdent.from_ident type_def.type_def_name)
            in

            let+ _ =
              Rewriter.List.iter variant_decl_list ~f:(fun variant_decl ->
                  let* _ =
                    Rewriter.List.iter variant_decl.variant_args ~f:(fun var_arg ->
                        let (data_type_destr : Module.destr_def) =
                          {
                            destr_name = var_arg.var_name;
                            destr_loc = var_arg.var_loc;
                            destr_arg = App (Var fully_qualified_tp_name, [], _tp_attr);
                            destr_return_type = var_arg.var_type;
                          }
                        in
                        Rewriter.introduce_symbol Module.(DestrDef data_type_destr))
                  in

                  let (data_type_constr : Module.constr_def) =
                    {
                      constr_name = variant_decl.variant_name;
                      constr_loc = variant_decl.variant_loc;
                      constr_return_type = App (Var fully_qualified_tp_name, [], _tp_attr);
                      constr_args = variant_decl.variant_args;
                    }
                  in

                  Rewriter.introduce_symbol Module.(ConstrDef data_type_constr))
            in
            Type.App (Data (fully_qualified_tp_name, variant_decl_list), [], _tp_attr)
        | App (Data _, _, _tp_attr) ->
            Error.error (Type.to_loc tp_expr) "Data types don't take arguments"
        | _ -> TypeExpr.process_type_expr tp_expr
      in

      let type_def = { type_def with type_def_expr = Some tp_expr } in
      Module.TypeDef type_def

(* A manifest field, `field f = M.g`, takes its type from the target rather
     than declaring one of its own; the ghost modifier, if written, must agree
     with the target's. *)
let process_alias_field (field : Module.field_def) (target : qual_ident) : Module.symbol t
    =
  let open Rewriter.Syntax in
  let* target, symbol = Rewriter.resolve_and_find target in
  let* symbol = Rewriter.Symbol.reify symbol in
  let target_field =
    match symbol with
    | Module.FieldDef target_field -> target_field
    | _ ->
        Error.type_error (QualIdent.to_loc target)
          (Printf.sprintf
             !"Expected a field on the right-hand side of 'field %{Ident} = ...', but \
               found %s %{QualIdent}"
             field.field_name (Symbol.kind symbol) target)
  in
  let _ =
    if Bool.(field.field_is_ghost <> target_field.field_is_ghost) then
      Error.type_error field.field_loc
        (Printf.sprintf
           !"Field %{Ident} is declared %s, but %{QualIdent} is %s"
           field.field_name
           (if field.field_is_ghost then "ghost" else "non-ghost")
           target
           (if target_field.field_is_ghost then "ghost" else "non-ghost"))
  in
  Rewriter.return
    (Module.FieldDef
       { field with field_type = target_field.field_type; field_alias = Some target })

let process_field (field : Module.field_def) : Module.symbol t =
  let open Rewriter.Syntax in
  match field.field_alias with
  | Some target -> process_alias_field field target
  | None ->
      let+ tp_expr =
        match field.field_type with
        | App (Var qual_ident, [], tp_attr) -> (
            let* fully_qualified_qual_ident, symbol =
              Rewriter.resolve_and_find qual_ident
            in
            match Rewriter.Symbol.orig_symbol symbol with
            | ModDef { mod_decl = { mod_decl_is_ra = true; _ }; _ } ->
                Rewriter.return @@ Type.App (Var fully_qualified_qual_ident, [], tp_attr)
            | _ -> TypeExpr.process_type_expr field.field_type)
        | _ -> TypeExpr.process_type_expr field.field_type
      in

      let field = { field with field_type = tp_expr } in
      Module.(FieldDef field)

let process_var (var : Stmt.var_def) : Module.symbol t =
  let open Rewriter.Syntax in
  let _ =
    if not var.var_decl.var_const then
      Error.type_error var.var_decl.var_loc
        "Modules and interfaces cannot have var members"
  in
  let* var_decl = TypeExpr.process_var_decl var.var_decl in
  let+ var_init =
    Rewriter.Option.map var.var_init ~f:(fun expr ->
        ExprTyping.process_expr expr var_decl.var_type)
  in
  let var_type =
    var_init |> Option.map ~f:Expr.to_type |> Option.value ~default:var_decl.var_type
  in
  let _ =
    if Type.equal var_type Type.any then
      Error.error var_decl.var_loc
      @@ Printf.sprintf "Type annotation missing for variable %s"
           (Ident.to_string var_decl.var_name)
  in
  let var_is_free = var.var_is_free in
  let (var : Stmt.var_def) =
    { var_decl = { var_decl with var_type }; var_init; var_is_free }
  in
  Module.(VarDef var)

let rec process_module (m : Module.t) : Module.t t =
  let open Rewriter.Syntax in
  let _ =
    Logs.info (fun mm -> mm !"Processing module %{Ident}" (Symbol.to_name (ModDef m)))
  in
  let () =
    let decl = m.mod_decl in
    if decl.mod_decl_is_sealed && decl.mod_decl_is_interface then
      Error.type_error decl.mod_decl_loc
        (Printf.sprintf
           !"Interface %{Ident} cannot be sealed with ':>'"
           decl.mod_decl_name)
  in

  let* sc = Rewriter.current_scope_children in
  Logs.debug (fun mm ->
      mm
        !"Processing module %{Ident}: scope_children: %a"
        (Symbol.to_name (ModDef m))
        (Print.pr_list_comma Ident.pr)
        (Hashtbl.keys sc));
  let* is_root =
    let+ tbl = Rewriter.get_table in
    (* Hashtbl.mem  *)
    Ident.(m.mod_decl.mod_decl_name = QualIdent.to_ident (SymbolTbl.root_ident tbl))
  in

  let process_instr = function
    | Module.SymbolDef symbol ->
        let* symbol_def =
          match symbol with
          | TypeDef type_def -> process_type_def type_def
          | VarDef var_def -> process_var var_def
          | FieldDef field_def -> process_field field_def
          | ConstrDef _ | DestrDef _ ->
              Rewriter.return symbol
              (* These should not occur directly in a module definition *)
          | CallDef call_def -> CallableTyping.process_callable call_def
          | ModDef mod_def ->
              let* _ = Rewriter.enter_module mod_def
              and* mod_def = process_module mod_def in
              let+ mod_def = Rewriter.exit_module mod_def in
              Module.ModDef mod_def
          | ModInst mod_inst ->
              (* A functor application `module M : I = F[args]` *)
              (* Get symbol of I *)
              let* mod_inst_type = Rewriter.resolve mod_inst.mod_inst_type in
              (* Resolve the functor `F` and pair up its formals with `args`,
                   wrapping any bare-type argument (e.g. `M[Int]`) into a
                   synthesized module implementing the formal's rep-typed
                   interface (see `ProgUtils.intros_rep_module`). This must
                   happen *before* `declare_symbol` below, since
                   `SymbolTbl.add_symbol` resolves every argument to an
                   already-existing module to build the instance's
                   substitution. *)
              let* mod_inst_def, to_check =
                match mod_inst.mod_inst_def with
                | None -> Rewriter.return (None, [])
                | Some (mod_inst_func, mod_inst_args) ->
                    (* Get qualified name of F and its symbol *)
                    let* qual_functor_ident, functor_symbol =
                      Rewriter.resolve_and_find mod_inst_func
                    in
                    (* Get formal parameters of F *)
                    let formals =
                      Rewriter.Symbol.extract functor_symbol
                        ~f:(fun is_instance subst -> function
                        | Ast.Module.ModDef mod_def when not is_instance ->
                            List.map mod_def.mod_decl.mod_decl_formals ~f:(fun formal ->
                                (formal, subst formal.mod_inst_type))
                        | _ -> [])
                    in
                    (* Pair up `args` and formals *)
                    let* args_and_formals =
                      match List.zip mod_inst_args formals with
                      | Ok res -> Rewriter.return res
                      | Unequal_lengths ->
                          arg_mismatch_error "Module"
                            (QualIdent.to_loc mod_inst_func)
                            (Type.Var mod_inst_func) (List.length formals)
                    in
                    let+ resolved_args =
                      Rewriter.List.map args_and_formals
                        ~f:(fun (arg, (formal, formal_iface)) ->
                          match arg with
                          | Module.ModArg qi -> Rewriter.return (qi, formal_iface)
                          | Module.TypeArg tp -> (
                              let* rep =
                                lift (ProgUtils.resolve_rep_ident formal_iface)
                              in
                              match rep with
                              | None ->
                                  Error.type_error (Type.to_loc tp)
                                    (Printf.sprintf
                                       !"Cannot pass a type as argument for parameter \
                                         %{Ident}: interface %{QualIdent} does not \
                                         declare a rep type"
                                       formal.mod_inst_name formal_iface)
                              | Some (interface_qual_ident, rep_ident) ->
                                  let* insert_scope, reference_scope =
                                    lift (ProgUtils.find_insertion_scope_for_types [ tp ])
                                  in
                                  let+ qi =
                                    lift
                                      (ProgUtils.get_or_intros_rep_module
                                         ~loc:(Type.to_loc tp)
                                         ~f:!Rewriter.process_symbol_ref ~insert_scope
                                         ~reference_scope ~interface_qual_ident ~rep_ident
                                         tp)
                                  in
                                  (qi, formal_iface)))
                    in
                    ( Some
                        ( qual_functor_ident,
                          List.map resolved_args ~f:(fun (qi, _) -> Module.ModArg qi) ),
                      (qual_functor_ident, mod_inst.mod_inst_type) :: resolved_args )
              in
              let symbol = Module.ModInst { mod_inst with mod_inst_type; mod_inst_def } in
              (* Only instantiations (`mod_inst_def = Some _`) are declared here;
                   abstract module parameters (`mod_inst_def = None`) are already
                   declared by the pre-declare pass above. *)
              let* _ =
                match mod_inst.mod_inst_def with
                | None -> Rewriter.return ()
                | Some _ -> lift (Rewriter.declare_symbol symbol)
              in
              (* Check that `args` satisfy module types of formals *)
              let+ _ =
                Rewriter.List.iter to_check ~f:(fun (m, i) ->
                    Interfaces.check_module_type m i)
              in
              symbol
        in
        let* () =
          Rewriter.Logs.debug (fun printers mm ->
              mm "Processing module %a: symbol: %a" Ident.pr (Symbol.to_name (ModDef m))
                printers.pr_symbol symbol_def)
        in
        let+ _ = Rewriter.set_symbol symbol_def in
        Module.SymbolDef symbol_def
    | Import import ->
        (* Handled by symbol table *)
        let* _ = Rewriter.import import in
        Rewriter.return (Module.Import import)
  in

  (* Add formal parameters to module definitions *)
  let mod_def_formals =
    List.map m.mod_decl.mod_decl_formals ~f:(fun mod_def_formal ->
        Module.SymbolDef (ModInst mod_def_formal))
  in
  let mod_def = mod_def_formals @ m.mod_def in
  let get_defined_symbols mod_def =
    List.fold mod_def
      ~init:(Set.empty (module Ident))
      ~f:(fun ids -> function
        | Module.SymbolDef symbol -> Set.add ids (Symbol.to_name symbol) | _ -> ids)
  in
  let defined_symbols = get_defined_symbols mod_def in

  let* mod_qual_ident =
    if is_root then Rewriter.return @@ QualIdent.from_ident (Symbol.to_name (ModDef m))
    else
      let _ =
        Logs.debug (fun mm ->
            mm "Typing.process_module: computing mod_qual_ident: %a" QualIdent.pr
              (QualIdent.from_ident (Symbol.to_name (ModDef m))))
      in

      Rewriter.resolve (QualIdent.from_ident (Symbol.to_name (ModDef m)))
  in
  (* merge symbol definitions from parent interface with those from current module
     * so that the dependency order between symbols is preserved *)
  (* The members inherited from interfaces, for [EditorAnnotations.record_inherited_members]. *)
  let inherited_members = ref [] in

  let merge_defs ~parent_status ~parent_is_interface parent_ident parent_mod_def mod_def =
    (* A non-callable member with no definition of its own. Mirrors the cases the
         abstract-member check below rejects in a non-interface module. Callables are
         left out: [Module.set_unit_free] never frees an abstract one, so a free
         callable without a body is one whose body freeing dropped. *)
    let symbol_is_abstract = function
      | Module.TypeDef { type_def_expr = None; _ }
      | ModInst { mod_inst_def = None; _ }
      | VarDef { var_decl = { var_const = true; _ }; var_init = None; _ } ->
          true
      | _ -> false
    in
    (* The standard library, and every included file, is force-marked [MachineFree] so
         it isn't re-verified for each program. That status describes the file, not the
         modules that implement its interfaces: an abstract member inherited from one
         into a concrete module must not arrive already free, or the module would owe
         neither a definition for it nor (for an inherited axiom) a proof of it against
         its own definitions -- which is how a module could claim to implement
         `ResourceAlgebra` while defining almost none of it.

         A `free` the user actually wrote stays [UserFree] and is left alone, so an
         interface may still declare a deliberately uninterpreted member that
         implementors inherit without defining (`free func`, `free val`, `free auto
         axiom`).

         Abstract callables never arrive free in the first place ([Module.set_unit_free]
         leaves them [NotFree]), so this only concerns types, values and module
         instances. Restricted to an *interface* parent, since a concrete module has no
         abstract members. *)
    let un_free_inherited symbol =
      match (parent_status, Symbol.free_status symbol) with
      | MachineFree, (NotFree | MachineFree)
        when parent_is_interface
             && (not m.mod_decl.mod_decl_is_interface)
             && symbol_is_abstract symbol ->
          Module.set_symbol_status NotFree symbol
      | _ -> symbol
    in
    let formals =
      List.fold_left
        ~init:(Set.empty (module Ident))
        ~f:(fun acc -> function
          | SymbolDef (ModInst mod_inst) -> Set.add acc mod_inst.mod_inst_name | _ -> acc)
        mod_def_formals
    in
    (*let _parent_defined_symbols = get_defined_symbols parent_mod_def in*)
    let rec merge_defs (merged, to_check, seen) = function
      | [], mod_def -> (List.rev_append merged mod_def, to_check)
      | Module.Import _ :: parent_mod_def, mod_def ->
          merge_defs (merged, to_check, seen) (parent_mod_def, mod_def)
      | Module.SymbolDef (ConstrDef _ | DestrDef _) :: parent_mod_def, mod_def
      | parent_mod_def, Module.SymbolDef (ConstrDef _ | DestrDef _) :: mod_def ->
          merge_defs (merged, to_check, seen) (parent_mod_def, mod_def)
      | Module.SymbolDef parent_symbol :: parent_mod_def, mod_def -> (
          let parent_symbol_ident = Symbol.to_name parent_symbol in
          let annotate_error_msg = function
            | Module.CallDef ({ call_decl; _ } as call) as symbol ->
                let annotate_spec spec =
                  let error =
                    ( Error.RelatedLoc,
                      Symbol.to_loc parent_symbol,
                      Printf.sprintf
                        !"%s %{Ident} inherited from %s %{QualIdent}.%{Ident}"
                        (Symbol.kind symbol |> String.capitalize)
                        parent_symbol_ident (Symbol.kind parent_symbol) parent_ident
                        parent_symbol_ident )
                  in
                  {
                    spec with
                    Stmt.spec_error =
                      Stmt.mk_const_spec_error error :: spec.Stmt.spec_error;
                  }
                in
                let call_decl_postcond =
                  List.map ~f:annotate_spec call_decl.call_decl_postcond
                in
                let call_decl_precond =
                  List.map ~f:annotate_spec call_decl.call_decl_precond
                in
                let call_decl =
                  {
                    call_decl with
                    call_decl_precond;
                    call_decl_postcond;
                    call_decl_loc = m.mod_decl.mod_decl_loc;
                  }
                in
                Module.CallDef { call with call_decl }
            | symbol -> symbol
          in
          if Set.mem formals parent_symbol_ident then
            (* case: parent_symbol is being abstracted over *)
            merge_defs
              ( merged,
                Map.add_exn to_check ~key:parent_symbol_ident ~data:parent_symbol,
                seen )
              (parent_mod_def, mod_def)
          else if
            (not (Set.mem defined_symbols parent_symbol_ident))
            && (Set.is_empty seen || List.is_empty mod_def)
          then (
            (* case: parent_symbol should be inherited now *)
            let _ =
              Logs.debug (fun m -> m !"Inheriting symbol %{Ident}" parent_symbol_ident)
            in
            inherited_members := (parent_ident, parent_symbol) :: !inherited_members;
            let parent_symbol = un_free_inherited parent_symbol in
            let parent_symbol =
              match parent_symbol with
              | CallDef call when not @@ Callable.is_abstract call ->
                  Logs.debug (fun m ->
                      m !"Making %{Ident} free." (Callable.to_ident call));
                  Module.CallDef (Callable.set_machine_free call)
              | CallDef ({ call_decl = { call_decl_kind = Lemma; _ }; _ } as call)
                when Callable.is_abstract call && not m.mod_decl.mod_decl_is_interface ->
                  let loc = m.mod_decl.mod_decl_loc in
                  (* Keep 'auto' flag for everything but RA associativity axioms *)
                  let auto =
                    call.call_decl.call_decl_is_auto
                    && String.(call.call_decl.call_decl_name |> Ident.name <> "compAssoc")
                  in
                  let call =
                    {
                      Callable.call_decl =
                        { call.call_decl with call_decl_is_auto = auto };
                      call_def = ProcDef { proc_body = Some (Stmt.mk_skip ~loc) };
                    }
                  in
                  let call =
                    if is_free m.mod_decl.mod_decl_status then
                      Callable.set_machine_free call
                    else call
                  in
                  annotate_error_msg (CallDef call)
              | ModDef mod_def -> ModDef (Module.set_machine_free mod_def)
              | _ -> annotate_error_msg parent_symbol
            in

            merge_defs
              (Module.SymbolDef parent_symbol :: merged, to_check, seen)
              (parent_mod_def, mod_def))
          else
            match mod_def with
            | Module.SymbolDef symbol :: mod_def ->
                let symbol_ident = Symbol.to_name symbol in
                if Set.mem seen symbol_ident then
                  (* case: symbol provides definition of another symbol that has already been seen earlier *)
                  merge_defs
                    ( Module.SymbolDef symbol :: merged,
                      to_check,
                      Set.remove seen symbol_ident )
                    (Module.SymbolDef parent_symbol :: parent_mod_def, mod_def)
                else if Ident.(parent_symbol_ident = symbol_ident) then
                  (* case: symbol provides definition of parent_symbol *)
                  merge_defs
                    ( Module.SymbolDef symbol :: merged,
                      Map.add_exn to_check ~key:symbol_ident ~data:parent_symbol,
                      seen )
                    (parent_mod_def, mod_def)
                else if Set.mem defined_symbols parent_symbol_ident then
                  (* case: parent_symbol is defined later in mod_def *)
                  merge_defs
                    ( merged,
                      Map.add_exn to_check ~key:parent_symbol_ident ~data:parent_symbol,
                      Set.add seen parent_symbol_ident )
                    (parent_mod_def, Module.SymbolDef symbol :: mod_def)
                else
                  (* case: symbol is newly declared symbol *)
                  merge_defs
                    (Module.SymbolDef symbol :: merged, to_check, seen)
                    (Module.SymbolDef parent_symbol :: parent_mod_def, mod_def)
            | def :: mod_def ->
                merge_defs
                  (def :: merged, to_check, seen)
                  (Module.SymbolDef parent_symbol :: parent_mod_def, mod_def)
            | [] -> assert false)
    in
    merge_defs
      ([], Map.empty (module Ident), Set.empty (module Ident))
      (parent_mod_def, mod_def)
  in

  (* Compute symbols that are inherited from parent interface, respectively, that need to be checked against the parent interface *)
  let* ( mod_decl_returns,
         mod_decl_interfaces,
         interface_ident,
         interface_formals,
         (merged_symbols, symbols_to_check) ) =
    (* Disjointness is decided on the parents as declared, *before* the
         self-renaming substitution below rewrites each parent's own name to this
         module -- after it, every parent appears to share this module as an
         ancestor. *)
    let* () =
      match m.mod_decl.mod_decl_returns with
      | [] | [ _ ] -> Rewriter.return ()
      | returns ->
          let+ parent_ancestors =
            Rewriter.List.map returns ~f:(fun (mid, _args) ->
                let* qual_ident, symbol = Rewriter.resolve_and_find mid in
                let+ symbol = Rewriter.Symbol.reify symbol in
                match symbol with
                | Module.ModDef interface ->
                    (mid, Set.add interface.mod_decl.mod_decl_interfaces qual_ident)
                | _ -> (mid, Set.singleton (module QualIdent) qual_ident))
          in
          Interfaces.check_parents_disjoint ~loc:m.mod_decl.mod_decl_loc parent_ancestors
    in
    let* parents =
      Rewriter.List.map m.mod_decl.mod_decl_returns ~f:(fun (mid, args) ->
          Logs.debug (fun mm ->
              mm
                !"Typing.process_module: module %{Ident}: checking return type \
                  %{QualIdent}"
                (Symbol.to_name (ModDef m)) mid);
          let* qual_interface_ident, interface_symbol = Rewriter.resolve_and_find mid in
          (* Formals of a parameterised parent are substituted by its
               arguments; then the parent's own name is rewritten to this
               module. Order matters: once `Base` has been rewritten to `M`, a
               later `Base.A -> Arg` mapping would no longer match. *)
          let* arg_subst =
            Rewriter.List.map args ~f:(function
              | Module.ModArg qi ->
                  let base = QualIdent.unqualify qi in
                  if
                    QualIdent.is_local qi
                    && List.exists m.mod_decl.mod_decl_formals ~f:(fun formal ->
                        Ident.equal formal.mod_inst_name base)
                  then
                    (* Argument naming one of this module's own formals, the
                         usual case. Formals are not in the symbol table yet
                         here, and the merged members end up in this module's
                         scope, so point at the formal directly. *)
                    Rewriter.return (QualIdent.append mod_qual_ident base)
                  else
                    let+ qi = Rewriter.resolve qi in
                    qi
              | Module.TypeArg tp ->
                  Error.type_error (Type.to_loc tp)
                    "An inherited interface must be applied to modules, not to bare \
                     types; name a module implementing the parameter's interface instead")
          in
          let interface_symbol =
            match interface_symbol with
            | _ when List.is_empty arg_subst -> interface_symbol
            | _ -> (
                let formals =
                  Rewriter.Symbol.extract interface_symbol
                    ~f:(fun _is_instance _subst -> function
                    | Ast.Module.ModDef mod_def -> mod_def.mod_decl.mod_decl_formals
                    | _ -> [])
                in
                match List.zip formals arg_subst with
                | Ok pairs ->
                    List.fold pairs ~init:interface_symbol ~f:(fun sym (formal, arg_qi) ->
                        Rewriter.Symbol.extend_subst
                          ( QualIdent.append qual_interface_ident formal.mod_inst_name,
                            QualIdent.to_list arg_qi )
                          sym)
                | Unequal_lengths ->
                    arg_mismatch_error "Interface" (QualIdent.to_loc mid) (Type.Var mid)
                      (List.length formals))
          in
          let interface_symbol =
            Rewriter.Symbol.extend_subst
              (qual_interface_ident, QualIdent.to_list mod_qual_ident)
              interface_symbol
          in

          (* Whether the parent is an interface has to be read here, off the
               symbol as resolved: reifying it below rebuilds the declaration and
               does not carry the flag through, so the reified copy reports false
               for every parent alike. *)
          let parent_is_interface =
            Rewriter.Symbol.extract interface_symbol ~f:(fun _ _ -> function
              | Ast.Module.ModDef md -> md.mod_decl.mod_decl_is_interface
              | _ -> false)
          in
          let* interface_symbol = Rewriter.Symbol.reify interface_symbol in
          let* () =
            Rewriter.Logs.debug (fun printers mm ->
                mm
                  !"Typing.process_module: %{Ident}: checking return type %a: reified; \n\
                   \ qual_interface_ident: %{QualIdent} \n\
                   \ mid: %{QualIdent}"
                  (Symbol.to_name (ModDef m)) printers.pr_symbol interface_symbol
                  qual_interface_ident mid)
          in
          Rewriter.return
            (qual_interface_ident, mid, arg_subst, parent_is_interface, interface_symbol))
    in
    let parent_defs =
      List.filter_map parents ~f:(function
        | qual_interface_ident, mid, args, parent_is_interface, ModDef interface ->
            Some (qual_interface_ident, mid, args, parent_is_interface, interface)
        | _ -> None)
    in
    match parent_defs with
    | [] ->
        let mod_ident = QualIdent.from_ident m.mod_decl.mod_decl_name in
        let interfaces =
          if is_root then m.mod_decl.mod_decl_interfaces
          else Set.add m.mod_decl.mod_decl_interfaces mod_qual_ident
        in
        Rewriter.return
          ([], interfaces, mod_ident, None, (m.mod_def, Map.empty (module Ident)))
    | first_parent :: _ ->
        (* Merge each parent in turn, threading the accumulated definition, so
             a later parent sees earlier parents' members as already defined. *)
        let returns, interfaces, formals, merged, to_check =
          List.fold parent_defs
            ~init:
              ([], Set.empty (module QualIdent), None, m.mod_def, Map.empty (module Ident))
            ~f:(fun
                (returns, interfaces, formals, mod_def, to_check)
                (qual_interface_ident, _mid, args, parent_is_interface, interface)
              ->
              let merged, to_check' =
                merge_defs ~parent_status:interface.mod_decl.mod_decl_status
                  ~parent_is_interface qual_interface_ident interface.mod_def mod_def
              in
              let to_check =
                Map.fold to_check' ~init:to_check ~f:(fun ~key ~data acc ->
                    match Map.add acc ~key ~data:(qual_interface_ident, data) with
                    | `Ok acc -> acc
                    | `Duplicate ->
                        Error.type_error m.mod_decl.mod_decl_loc
                          (Printf.sprintf
                             !"Member %{Ident} is declared by more than one of the \
                               interfaces %s implements; a module cannot inherit two \
                               declarations of the same name"
                             key
                             (Ident.to_string
                                (ProgUtils.source_module_name m.mod_decl.mod_decl_name))))
              in
              (* Only an unapplied parameterised parent imposes its formals on
                   this module; an applied one supplied them as arguments. *)
              let formals =
                match (formals, args) with
                | Some _, _ | None, _ :: _ -> formals
                | None, [] ->
                    if List.is_empty interface.mod_decl.mod_decl_formals then None
                    else Some interface.mod_decl.mod_decl_formals
              in
              ( (qual_interface_ident, List.map args ~f:(fun qi -> Module.ModArg qi))
                :: returns,
                Set.union interfaces
                  (Set.add interface.mod_decl.mod_decl_interfaces qual_interface_ident),
                formals,
                merged,
                to_check ))
        in
        let qual_first, _, _, _, _ = first_parent in
        Rewriter.return
          (List.rev returns, interfaces, qual_first, formals, (merged, to_check))
  in

  (* A callable that omits its contract -- no `requires`, `ensures` or `opens` --
       inherits the contract of the interface member it implements, with the
       interface's parameters renamed to its own. *)
  let inherit_contract = function
    | Module.SymbolDef (CallDef ({ call_decl; _ } as call)) as instr
      when List.is_empty call_decl.call_decl_precond
           && List.is_empty call_decl.call_decl_postcond
           && Option.is_none call_decl.call_decl_opens -> (
        match Map.find symbols_to_check call_decl.call_decl_name with
        | Some (interface_ident, (CallDef orig as orig_symbol)) -> (
            let orig_decl = orig.call_decl in
            let renaming =
              List.zip
                (orig_decl.call_decl_formals @ orig_decl.call_decl_returns)
                (call_decl.call_decl_formals @ call_decl.call_decl_returns)
            in
            match renaming with
            | Unequal_lengths -> instr
            | Ok pairs ->
                let map =
                  List.fold pairs
                    ~init:(Map.empty (module QualIdent))
                    ~f:(fun map ((orig_var : var_decl), (var : var_decl)) ->
                      Map.set map
                        ~key:(QualIdent.from_ident orig_var.var_name)
                        ~data:(Expr.from_var_decl var))
                in
                let rename e = Expr.alpha_renaming e map in
                let inherited =
                  ( Error.RelatedLoc,
                    Symbol.to_loc orig_symbol,
                    Printf.sprintf
                      !"Contract inherited from %s %{QualIdent}.%{Ident}"
                      (Symbol.kind orig_symbol) interface_ident call_decl.call_decl_name
                  )
                in
                let inherit_spec (spec : Stmt.spec) =
                  {
                    spec with
                    spec_form = rename spec.spec_form;
                    spec_trigs = List.map spec.spec_trigs ~f:(List.map ~f:rename);
                    spec_error = spec.spec_error @ [ Stmt.mk_const_spec_error inherited ];
                  }
                in
                let call_decl =
                  {
                    call_decl with
                    call_decl_precond =
                      List.map orig_decl.call_decl_precond ~f:inherit_spec;
                    call_decl_postcond =
                      List.map orig_decl.call_decl_postcond ~f:inherit_spec;
                    call_decl_opens =
                      Option.map orig_decl.call_decl_opens
                        ~f:(List.map ~f:(fun (qi, args) -> (qi, List.map args ~f:rename)));
                  }
                in
                let () =
                  EditorAnnotations.record_inherited_contract
                    ~member:call_decl.call_decl_name ~source:interface_ident
                    ~source_loc:(Symbol.to_loc orig_symbol) ~renaming:pairs orig_decl
                in
                Module.SymbolDef (CallDef { call with call_decl }))
        | _ -> instr)
    | instr -> instr
  in
  let merged_symbols = List.map merged_symbols ~f:inherit_contract in
  let () =
    EditorAnnotations.record_inherited_members ~module_ident:mod_qual_ident
      ~module_loc:m.mod_decl.mod_decl_loc !inherited_members
  in
  let mod_def = mod_def_formals @ merged_symbols in
  let _ = Logs.info (fun mm -> mm !"Merged in %{Ident}" (Symbol.to_name (ModDef m))) in
  let _ =
    List.iter
      ~f:(function
        | SymbolDef symbol -> Logs.info (fun m -> m !"%{Ident}" (Symbol.to_name symbol))
        | _ -> ())
      mod_def
  in
  (* Find rep type and add it to module declaration *)
  let mod_decl_rep =
    List.fold_left mod_def ~init:None ~f:(fun rep_type -> function
      | SymbolDef (TypeDef type_def) when type_def.type_def_rep ->
          Option.map_or_else
            ~m:(fun _ ->
              Error.syntax_error type_def.type_def_loc
                (Printf.sprintf
                   !"Found more than one rep type in module %{Ident}"
                   (ProgUtils.source_module_name m.mod_decl.mod_decl_name)))
            ~e:(fun () -> Some type_def.type_def_name)
            () rep_type
      | _ -> rep_type)
  in

  (* Determine whether this module is an RA *)
  let _ =
    Set.iter mod_decl_interfaces ~f:(fun qid ->
        Logs.debug (fun m -> m !"%{QualIdent}" qid))
  in
  let* mod_decl_is_ra =
    Rewriter.List.exists (Set.to_list mod_decl_interfaces) ~f:(fun interface_ident ->
        let+ _qual_interface_ident, interface_symbol =
          Rewriter.resolve_and_find interface_ident
        in
        Rewriter.Symbol.extract interface_symbol ~f:(fun _ _ -> function
          | Module.ModDef mod_def -> mod_def.mod_decl.mod_decl_is_ra
          | _ -> false))
  in
  let mod_decl_is_ra =
    mod_decl_is_ra || QualIdent.(mod_qual_ident = Ast.Predefs.lib_ra_mod_qual_ident)
  in

  (* Logs.debug (fun mm -> mm !"Typing.process_module: module %{Ident}: mod_decl_is_ra: %{Bool}" (Symbol.to_name (ModDef m)) mod_decl_is_ra); *)

  (* Add return type to module declaration *)
  let* mod_decl_formals =
    Rewriter.List.map m.mod_decl.mod_decl_formals ~f:(fun mod_inst ->
        let+ mod_inst_type = Rewriter.resolve mod_inst.mod_inst_type in
        { mod_inst with mod_inst_type })
  in

  let mod_decl =
    {
      m.mod_decl with
      mod_decl_rep;
      mod_decl_returns;
      mod_decl_formals;
      mod_decl_interfaces;
      mod_decl_is_ra;
    }
  in

  (* Make sure that the module preserves the parameters of its interface *)
  let _ =
    let interface_formals = Option.value interface_formals ~default:[] in
    match interface_formals with
    | [] -> ()
    | _ -> (
        let res =
          List.iter2 mod_decl.mod_decl_formals interface_formals ~f:(fun param oparam ->
              if
                Ident.(param.mod_inst_name <> oparam.mod_inst_name)
                || QualIdent.(param.mod_inst_type <> oparam.mod_inst_type)
              then
                Error.type_error param.mod_inst_loc
                  (Printf.sprintf
                     !"Parameter %{Ident} of %s %{Ident} does not match declaration of \
                       parameter %{Ident} of interface %{QualIdent}"
                     param.mod_inst_name (Symbol.kind (ModDef m)) mod_decl.mod_decl_name
                     oparam.mod_inst_name interface_ident))
        in
        match res with
        | Ok list -> list
        | Unequal_lengths ->
            param_mismatch_error "Interface"
              (Ident.to_loc mod_decl.mod_decl_name)
              (QualIdent.to_string interface_ident)
              (List.length interface_formals))
  in

  let* _ =
    Rewriter.List.iter mod_def ~f:(function
      | Module.SymbolDef (ModInst { mod_inst_def = Some _; _ }) | Module.Import _ ->
          Rewriter.return ()
      | Module.SymbolDef symbol -> lift (Rewriter.declare_symbol symbol))
  in

  (* Check and rewrite all symbols *)
  let* mod_def = Rewriter.List.map merged_symbols ~f:process_instr in

  (* Check symbols against what is specified in the interface *)
  let manifest_subst =
    List.fold mod_def
      ~init:(Map.empty (module QualIdent))
      ~f:(fun acc -> function
        | Module.SymbolDef (FieldDef { field_name; field_alias = Some target; _ }) ->
            Map.set acc ~key:(QualIdent.append mod_qual_ident field_name) ~data:target
        | _ -> acc)
  in
  let* _ =
    Rewriter.List.iter mod_def ~f:(function
      | SymbolDef symbol ->
          let ident = Symbol.to_name symbol in
          Map.find symbols_to_check ident
          |> Rewriter.Option.iter ~f:(fun (owning_interface, orig_symbol) ->
              Interfaces.check_implements_symbol ~manifest_subst owning_interface symbol
                orig_symbol)
      | _ -> Rewriter.return ())
  in

  (* Check whether modules are indeed modules *)
  let* _ =
    if not mod_decl.mod_decl_is_interface then
      Rewriter.List.iter mod_def ~f:(function
        | Import _ -> Rewriter.return ()
        | SymbolDef symbol when not (Symbol.is_free symbol) -> (
            match symbol with
            | TypeDef { type_def_expr = None; _ }
            | ModInst { mod_inst_def = None; _ }
            | VarDef { var_decl = { var_const = true; _ }; var_init = None; _ }
            | CallDef
                {
                  call_def = ProcDef { proc_body = None } | FuncDef { func_body = None };
                  call_decl = { call_decl_status = NotFree; _ };
                } ->
                if Ident.(mod_decl.mod_decl_name = Predefs.prog_ident) then
                  Error.type_error (Symbol.to_loc symbol)
                    (Printf.sprintf
                       !"The %s %{Ident} cannot be abstract here. An abstract member can \
                         only be declared in an interface"
                       (Symbol.kind symbol) (Symbol.to_name symbol))
                else
                  Error.type_error mod_decl.mod_decl_loc
                    (Printf.sprintf
                       !"Module %{Ident} must be declared as an interface. The %s \
                         %{Ident} is still abstract"
                       (ProgUtils.source_module_name mod_decl.mod_decl_name)
                       (Symbol.kind symbol) (Symbol.to_name symbol))
            | ModInst
                {
                  mod_inst_def = Some (mod_inst_func, _);
                  mod_inst_is_interface = false;
                  _;
                } -> (
                let+ mod_inst_symbol = Rewriter.find_and_reify mod_inst_func in
                match mod_inst_symbol with
                | Module.ModDef mdef ->
                    if mdef.mod_decl.mod_decl_is_interface then
                      Error.type_error (Symbol.to_loc symbol)
                        (Printf.sprintf
                           !"Module %{Ident} must be declared as an interface"
                           (ProgUtils.source_module_name (Symbol.to_name symbol)))
                | _ -> ())
            | _ -> Rewriter.return ())
        | _ -> Rewriter.return ())
    else Rewriter.return ()
  in
  (* [Library.WordSized] declares nothing but a representation type, so on its own it
       would constrain nothing; what it means is checked here, structurally, on whatever
       type an implementation supplies. This is the one interface the front end knows by
       name, and it is deliberate: an atomic primitive compiles to a single instruction
       over a single machine word, which is a claim about the representation that no
       amount of declared members could express.

       "Word-sized" is Int, Bool or Ref, or a sum of those small enough to carry a tag:
       at most four constructors, each taking at most one base-type argument. It says
       nothing about value ranges -- Raven's Int is the mathematical integers, so a bound
       like `0 <= x < 2^62` would be unsatisfiable and would make the interface
       unimplementable. Interfaces are exempt: their rep type is abstract, and it is the
       implementation that has to answer for it.

       Runs here, over the processed members, rather than beside the other declaration
       checks above: the rep type is read off its own definition, which is only in its
       final form once [process_instr] has been over it. *)
  let* () =
    let rep_def =
      match mod_decl.mod_decl_rep with
      | None -> None
      | Some rep_ident ->
          List.find_map mod_def ~f:(function
            | Module.SymbolDef (TypeDef { type_def_name; type_def_expr = Some tp; _ })
              when Ident.equal type_def_name rep_ident ->
                Some tp
            | _ -> None)
    in
    match rep_def with
    | Some rep_type
      when (not mod_decl.mod_decl_is_interface)
           && Set.mem mod_decl.mod_decl_interfaces Predefs.lib_word_sized_mod_qual_ident
      ->
        let* is_word_sized = is_type_word_sized rep_type in
        if is_word_sized then Rewriter.return ()
        else
          let* printers = Rewriter.current_printers in
          Error.type_error mod_decl.mod_decl_loc
            (Printf.sprintf
               !"`%s` is not word-sized, so it cannot implement %{QualIdent}. An atomic \
                 primitive operates on a single machine word: Int, Bool, Ref, or a data \
                 type with at most four constructors each taking at most one of those"
               (Print.string_of_format printers.pr_type rep_type)
               Predefs.lib_word_sized_mod_qual_ident)
    | _ -> Rewriter.return ()
  in

  let _ =
    Logs.debug (fun mm ->
        mm !"Done with processing module %{Ident}" (Symbol.to_name (ModDef m)))
  in
  let* () =
    Rewriter.Logs.debug (fun printers mm ->
        mm "%a" printers.pr_symbol (ModDef Module.{ mod_decl; mod_def }))
  in
  Rewriter.return Module.{ mod_decl; mod_def }
