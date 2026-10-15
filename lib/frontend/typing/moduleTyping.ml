(** Type checking of modules and their type, field and value members. *)

open Base
open Ast
open Util
open TypingMonad
open TypingErrors

(** Whether [typ] is word-sized: a base type (Int, Bool, Ref), or a data type with at most
    four constructors, each with at most one base-type argument, which leaves two bits for
    the tag. *)
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

let check_type_def (type_def : Module.type_def) : Module.symbol t =
  let open Rewriter.Syntax in
  Logs.debug (fun m ->
      m "ModuleTyping.check_type_def: Start processing type_def: %a" Ident.pr
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
                data_type_without_constructors_error (Type.to_loc tp_expr)
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
                          duplicate_constructor_error
                            (Ident.to_loc var_arg.var_name)
                            tp_expr))
            in

            let* variant_decl_list =
              Rewriter.List.map variant_decl_list ~f:(fun variant_decl ->
                  let+ variant_args =
                    Rewriter.List.map variant_decl.variant_args ~f:(fun var_decl ->
                        TypeExpr.check_var_decl var_decl)
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
        | App (Data _, _, _tp_attr) -> data_type_arguments_error (Type.to_loc tp_expr)
        | _ -> TypeExpr.check tp_expr
      in

      let type_def = { type_def with type_def_expr = Some tp_expr } in
      Module.TypeDef type_def

(* A manifest field, `field f = M.g`, takes its type from `M.g`; a ghost modifier must
   agree with it. *)
let check_alias_field (field : Module.field_def) (target : qual_ident) : Module.symbol t =
  let open Rewriter.Syntax in
  let* target, symbol = Rewriter.resolve_and_find target in
  let* symbol = Rewriter.Symbol.reify symbol in
  let target_field =
    match symbol with
    | Module.FieldDef target_field -> target_field
    | _ ->
        manifest_field_target_error (QualIdent.to_loc target) field.field_name
          (Symbol.kind symbol) target
  in
  let _ =
    if Bool.(field.field_is_ghost <> target_field.field_is_ghost) then
      manifest_field_ghost_error field.field_loc field.field_name
        ~ghost:field.field_is_ghost target ~target_ghost:target_field.field_is_ghost
  in
  Rewriter.return
    (Module.FieldDef
       { field with field_type = target_field.field_type; field_alias = Some target })

let check_field (field : Module.field_def) : Module.symbol t =
  let open Rewriter.Syntax in
  match field.field_alias with
  | Some target -> check_alias_field field target
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
            | _ -> TypeExpr.check field.field_type)
        | _ -> TypeExpr.check field.field_type
      in

      let field = { field with field_type = tp_expr } in
      Module.(FieldDef field)

let check_var (var : Stmt.var_def) : Module.symbol t =
  let open Rewriter.Syntax in
  let _ = if not var.var_decl.var_const then var_member_error var.var_decl.var_loc in
  let* var_decl = TypeExpr.check_var_decl var.var_decl in
  let+ var_init =
    Rewriter.Option.map var.var_init ~f:(fun expr ->
        ExprTyping.check expr var_decl.var_type)
  in
  let var_type =
    var_init |> Option.map ~f:Expr.to_type |> Option.value ~default:var_decl.var_type
  in
  let _ =
    if Type.equal var_type Type.any then
      missing_type_annotation_error var_decl.var_loc var_decl.var_name
  in
  let var_is_free = var.var_is_free in
  let (var : Stmt.var_def) =
    { var_decl = { var_decl with var_type }; var_init; var_is_free }
  in
  Module.(VarDef var)

(** A module that is not an interface may not have abstract members, nor instances of an
    interface. *)
let check_no_abstract_members (mod_decl : Module.module_decl)
    (mod_def : Module.module_instr list) : unit t =
  let open Rewriter.Syntax in
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
                abstract_in_program_error (Symbol.to_loc symbol) (Symbol.kind symbol)
                  (Symbol.to_name symbol)
              else
                still_abstract_error mod_decl.mod_decl_loc
                  (ProgUtils.source_module_name mod_decl.mod_decl_name)
                  (Symbol.kind symbol) (Symbol.to_name symbol)
          | ModInst
              { mod_inst_def = Some (mod_inst_func, _); mod_inst_is_interface = false; _ }
            -> (
              let+ mod_inst_symbol = Rewriter.find_and_reify mod_inst_func in
              match mod_inst_symbol with
              | Module.ModDef mdef ->
                  if mdef.mod_decl.mod_decl_is_interface then
                    must_be_interface_error (Symbol.to_loc symbol)
                      (ProgUtils.source_module_name (Symbol.to_name symbol))
              | _ -> ())
          | _ -> Rewriter.return ())
      | _ -> Rewriter.return ())
  else Rewriter.return ()

(** What [Library.WordSized] means is checked here, on the implementation's rep type: an
    atomic primitive works on a single machine word, which no declared member can express.
    The check concerns the representation, not value ranges, since Int is unbounded.
    Interfaces are exempt, as their rep type is abstract. It runs after [check_instr],
    which brings the rep type into its final form. *)
let check_word_sized (mod_decl : Module.module_decl) (mod_def : Module.module_instr list)
    : unit t =
  let open Rewriter.Syntax in
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
         && Set.mem mod_decl.mod_decl_interfaces Predefs.lib_word_sized_mod_qual_ident ->
      let* is_word_sized = is_type_word_sized rep_type in
      if is_word_sized then Rewriter.return ()
      else
        let* printers = Rewriter.current_printers in
        not_word_sized_error mod_decl.mod_decl_loc
          (Print.string_of_format printers.pr_type rep_type)
          Predefs.lib_word_sized_mod_qual_ident
  | _ -> Rewriter.return ()

let assign_function_identities (instrs : Module.module_instr list) =
  let open Module in
  let counts, taken =
    List.fold instrs
      ~init:(Map.empty (module Ident), Set.empty (module Ident))
      ~f:(fun (counts, taken) instr ->
        match instr with
        | SymbolDef symbol ->
            let taken = Set.add taken (Symbol.to_name symbol) in
            let counts =
              match symbol with
              | CallDef call when Poly.(Callable.kind call = Func) ->
                  Map.update counts (Callable.source_ident call) ~f:(fun count ->
                      Option.value count ~default:0 + 1)
              | _ -> counts
            in
            (counts, taken)
        | Import _ -> (counts, taken))
  in
  let _, instrs =
    List.fold_map instrs ~init:taken ~f:(fun taken instr ->
        match instr with
        | SymbolDef (CallDef call)
          when Poly.(Callable.kind call = Func)
               && Option.is_none call.call_decl.call_decl_source_name
               && Map.find_exn counts (Callable.source_ident call) > 1 ->
            let source = Callable.source_ident call in
            let rec fresh index =
              let id = Ident.make (Ident.to_loc source) (Ident.name source) index in
              if Set.mem taken id then fresh (index + 1) else id
            in
            let id = fresh 1 in
            let call_decl =
              {
                call.call_decl with
                call_decl_name = id;
                call_decl_source_name = Some source;
              }
            in
            (Set.add taken id, SymbolDef (CallDef { call with call_decl }))
        | _ -> (taken, instr))
  in
  instrs

let check_function_signatures (instrs : Module.module_instr list) =
  let open Rewriter.Syntax in
  let+ _ =
    Rewriter.List.fold_left instrs
      ~init:(Map.empty (module Ident))
      ~f:(fun signatures instr ->
        match instr with
        | SymbolDef (CallDef call)
          when Poly.(Callable.kind call = Func)
               && Option.is_some call.call_decl.call_decl_source_name ->
            let* types =
              Rewriter.List.map call.call_decl.call_decl_formals ~f:(fun formal ->
                  let+ typ = TypeExpr.expand_type_expr formal.Type.var_type in
                  Type.set_ghost false typ)
            in
            let source = Callable.source_ident call in
            let previous = Map.find signatures source |> Option.value ~default:[] in
            if List.exists previous ~f:(List.equal Type.equal types) then
              duplicate_overload_error (Callable.to_loc call) source;
            Rewriter.return (Map.set signatures ~key:source ~data:(types :: previous))
        | _ -> Rewriter.return signatures)
  in
  ()

let rec check (m : Module.t) : Module.t t =
  let open Rewriter.Syntax in
  let m = { m with mod_def = assign_function_identities m.mod_def } in
  let _ =
    Logs.info (fun mm -> mm !"Processing module %{Ident}" (Symbol.to_name (ModDef m)))
  in
  (* Only a module can be sealed. *)
  let () =
    let decl = m.mod_decl in
    if decl.mod_decl_is_sealed && decl.mod_decl_is_interface then
      sealed_interface_error decl.mod_decl_loc decl.mod_decl_name
  in

  let* sc = Rewriter.current_scope_children in
  Logs.debug (fun mm ->
      mm
        !"Processing module %{Ident}: scope_children: %a"
        (Symbol.to_name (ModDef m))
        (Print.pr_list_comma Ident.pr)
        (Hashtbl.keys sc));
  (* Whether [m] is the root module of the symbol table. *)
  let* is_root =
    let+ root = Rewriter.root_scope_id in
    Ident.(m.mod_decl.mod_decl_name = QualIdent.to_ident root)
  in

  (* Add formal parameters to module definitions *)
  let mod_def_formals =
    List.map m.mod_decl.mod_decl_formals ~f:(fun mod_def_formal ->
        Module.SymbolDef (ModInst mod_def_formal))
  in
  let mod_def = mod_def_formals @ m.mod_def in
  (* The names of the members of [mod_def]. *)
  let get_defined_symbols mod_def =
    List.fold mod_def
      ~init:(Set.empty (module Ident))
      ~f:(fun ids -> function
        | Module.SymbolDef symbol -> Set.add ids (Symbol.to_name symbol) | _ -> ids)
  in
  let defined_symbols = get_defined_symbols mod_def in

  (* The qualified name of [m]. *)
  let* mod_qual_ident =
    if is_root then Rewriter.return @@ QualIdent.from_ident (Symbol.to_name (ModDef m))
    else
      let _ =
        Logs.debug (fun mm ->
            mm "ModuleTyping.check: computing mod_qual_ident: %a" QualIdent.pr
              (QualIdent.from_ident (Symbol.to_name (ModDef m))))
      in

      Rewriter.resolve (QualIdent.from_ident (Symbol.to_name (ModDef m)))
  in
  (* The formals and types are declared before the other members. *)
  let type_headers =
    List.filter m.mod_def ~f:(function
      | Module.SymbolDef (TypeDef _) -> true
      | _ -> false)
  in
  let header_names = get_defined_symbols (mod_def_formals @ type_headers) in
  let* () =
    Rewriter.List.iter (mod_def_formals @ type_headers) ~f:(function
      | Module.SymbolDef symbol -> lift (Rewriter.declare_symbol symbol)
      | Module.Import _ -> Rewriter.return ())
  in
  (* Merge in the members of the parents: those inherited, and those to check against
     the interfaces. *)
  let* ( mod_decl_returns,
         mod_decl_interfaces,
         interface_ident,
         interface_formals,
         (merged_symbols, symbols_to_check, inherited_members) ) =
    Interfaces.merge_parents ~m ~is_root ~mod_qual_ident ~mod_def ~mod_def_formals
      ~defined_symbols
  in

  (* Members without a contract inherit the one of the interface member they implement. *)
  let merged_symbols =
    List.map merged_symbols ~f:(Interfaces.inherit_contract symbols_to_check)
  in
  let () =
    EditorAnnotations.record_inherited_members ~module_ident:mod_qual_ident
      ~module_loc:m.mod_decl.mod_decl_loc inherited_members
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
              multiple_rep_types_error type_def.type_def_loc
                (ProgUtils.source_module_name m.mod_decl.mod_decl_name))
            ~e:(fun () -> Some type_def.type_def_name)
            () rep_type
      | _ -> rep_type)
  in

  (* Determine whether this module is an RA *)
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

  (* The formals, with their interfaces resolved. *)
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
                parameter_mismatch_error param.mod_inst_loc param.mod_inst_name
                  (Symbol.kind (ModDef m)) mod_decl.mod_decl_name oparam.mod_inst_name
                  interface_ident)
        in
        match res with
        | Ok list -> list
        | Unequal_lengths ->
            param_mismatch_error "Interface"
              (Ident.to_loc mod_decl.mod_decl_name)
              interface_ident
              (List.length interface_formals))
  in

  (* Declare the remaining members. An instance with a definition is declared when it is
     checked, once its arguments are known. *)
  let* _ =
    Rewriter.List.iter merged_symbols ~f:(function
      | Module.SymbolDef (ModInst { mod_inst_def = Some _; _ }) | Module.Import _ ->
          Rewriter.return ()
      | Module.SymbolDef symbol ->
          if Set.mem header_names (Symbol.to_name symbol) then Rewriter.return ()
          else lift (Rewriter.declare_symbol symbol))
  in

  (* The parameter and return types of overloaded functions are checked before the members
     and recorded in the symbol table. *)
  let* merged_symbols =
    Rewriter.List.map merged_symbols ~f:(function
      | Module.SymbolDef (CallDef call)
        when Option.is_some call.call_decl.call_decl_source_name ->
          let* _ = Rewriter.enter_callable call in
          let* formals =
            Rewriter.List.map call.call_decl.call_decl_formals ~f:TypeExpr.check_var_decl
          in
          let* returns =
            Rewriter.List.map call.call_decl.call_decl_returns ~f:TypeExpr.check_var_decl
          in
          let call =
            {
              call with
              call_decl =
                {
                  call.call_decl with
                  call_decl_formals = formals;
                  call_decl_returns = returns;
                };
            }
          in
          let* call = Rewriter.exit_callable call in
          let+ _ = Rewriter.set_symbol (Module.CallDef call) in
          Module.SymbolDef (CallDef call)
      | instr -> Rewriter.return instr)
  in

  (* Members are checked in order. A module's own members, and a module instance, become
     known only once it is checked, so a module must be defined before it is used. This
     rules out mutually recursive modules, which would complicate the semantics of the
     module system. *)
  let* mod_def = Rewriter.List.map merged_symbols ~f:(check_instr m) in
  let* () = check_function_signatures mod_def in

  (* Check symbols against what is specified in the interface *)
  let manifest_subst =
    (* Fields that stand for another field, by their qualified names. *)
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

  (* Rules that depend on the whole module. *)
  let* () = check_no_abstract_members mod_decl mod_def in
  let* () = check_word_sized mod_decl mod_def in

  let _ =
    Logs.debug (fun mm ->
        mm !"Done with processing module %{Ident}" (Symbol.to_name (ModDef m)))
  in
  let* () =
    Rewriter.Logs.debug (fun printers mm ->
        mm "%a" printers.pr_symbol (ModDef Module.{ mod_decl; mod_def }))
  in
  Rewriter.return Module.{ mod_decl; mod_def }

(** Checks the member [instr] of [m]. *)
and check_instr (m : Module.t) (instr : Module.module_instr) : Module.module_instr t =
  let open Rewriter.Syntax in
  match instr with
  | Module.SymbolDef symbol ->
      let* symbol_def =
        match symbol with
        | TypeDef type_def -> check_type_def type_def
        | VarDef var_def -> check_var var_def
        | FieldDef field_def -> check_field field_def
        | ConstrDef _ | DestrDef _ ->
            Rewriter.return symbol
            (* These should not occur directly in a module definition *)
        | CallDef call_def -> CallableTyping.check call_def
        | ModDef mod_def ->
            let* _ = Rewriter.enter_module mod_def and* mod_def = check mod_def in
            let+ mod_def = Rewriter.exit_module mod_def in
            Module.ModDef mod_def
        | ModInst mod_inst ->
            (* A functor application `module M : I = F[args]` *)
            (* Get symbol of I *)
            let* mod_inst_type = Rewriter.resolve mod_inst.mod_inst_type in
            (* Resolves the functor `F` and pairs its formals with `args`, wrapping a
                 bare type argument (e.g. `M[Int]`) into a rep module (see
                 [ProgUtils.intros_rep_module]). This precedes [declare_symbol], as
                 [SymbolTbl.add_symbol] needs the argument modules. *)
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
                        | Module.TypeArg tp ->
                            let+ qi =
                              Interfaces.rep_module_of_type_arg formal formal_iface tp
                            in
                            (qi, formal_iface))
                  in
                  ( Some
                      ( qual_functor_ident,
                        List.map resolved_args ~f:(fun (qi, _) -> Module.ModArg qi) ),
                    (qual_functor_ident, mod_inst.mod_inst_type) :: resolved_args )
            in
            let symbol = Module.ModInst { mod_inst with mod_inst_type; mod_inst_def } in
            (* Only instances are declared here; abstract module parameters are declared
                 by the pass above. *)
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
