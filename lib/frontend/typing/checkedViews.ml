(** Verified adapters for explicit module views; nominal argument checks stay unchanged.
*)

open Base
open Ast
open Util
open TypingMonad

let unsupported loc message = Error.type_error loc ("Checked module view: " ^ message)

let rec has_token (Type.App (head, args, _)) =
  (match head with Type.AtomicToken _ -> true | _ -> false)
  || List.exists args ~f:has_token

let filter_map values ~f =
  let open Rewriter.Syntax in
  let+ values = Rewriter.List.map values ~f in
  List.filter_opt values

let requalify source target name =
  QualIdent.requalify [ (source, QualIdent.to_list target) ] name

let rec map_symbol source target symbol =
  let open Rewriter.Syntax in
  let f = requalify source target in
  match symbol with
  | Module.CallDef call ->
      let declaration = call.call_decl in
      let parameters =
        Rewriter.List.map ~f:(fun p ->
            let+ var_type = lift (Rewriter.Type.rewrite_qual_idents ~f p.Type.var_type) in
            { p with var_type })
      in
      let specs =
        Rewriter.List.map ~f:(fun spec ->
            let* spec_form =
              lift (Rewriter.Expr.rewrite_qual_idents ~f spec.Stmt.spec_form)
            in
            let+ spec_trigs =
              Rewriter.List.map spec.spec_trigs
                ~f:
                  (Rewriter.List.map ~f:(fun e ->
                       lift (Rewriter.Expr.rewrite_qual_idents ~f e)))
            in
            { spec with spec_form; spec_trigs })
      in
      let* call_decl_formals = parameters declaration.call_decl_formals in
      let* call_decl_returns = parameters declaration.call_decl_returns in
      let* call_decl_precond = specs declaration.call_decl_precond in
      let* call_decl_postcond = specs declaration.call_decl_postcond in
      let+ call_decl_opens =
        Rewriter.Option.map declaration.call_decl_opens ~f:(fun clause ->
            let+ opens_entries =
              Rewriter.List.map clause.Callable.opens_entries ~f:(fun (head, args) ->
                  let+ args =
                    Rewriter.List.map args ~f:(fun e ->
                        lift (Rewriter.Expr.rewrite_qual_idents ~f e))
                  in
                  (Callable.map_mask_head head ~f, args))
            in
            { clause with opens_entries })
      in
      Module.CallDef
        {
          call with
          call_decl =
            {
              declaration with
              call_decl_formals;
              call_decl_returns;
              call_decl_precond;
              call_decl_postcond;
              call_decl_opens;
              call_decl_loc_params = List.map declaration.call_decl_loc_params ~f;
            };
        }
  | Module.ModDef definition ->
      let+ mod_def =
        Rewriter.List.map definition.mod_def ~f:(function
          | Module.SymbolDef member ->
              let+ member = map_symbol source target member in
              Module.SymbolDef member
          | Module.Import directive -> Rewriter.return (Module.Import directive))
      in
      Module.ModDef { definition with mod_def }
  | _ -> lift (Rewriter.Module.rewrite_qual_idents_in_symbol ~f symbol)

let parameters_equal context instances (call : Callable.t) left right =
  let open Rewriter.Syntax in
  match List.zip left right with
  | Unequal_lengths -> Rewriter.return false
  | Ok pairs ->
      let normalize parameters =
        let* parameters =
          Rewriter.List.map parameters ~f:(fun p ->
              let+ var_type =
                lift
                  (Rewriter.Type.rewrite_qual_idents
                     ~f:(OverloadMatching.rename_instance instances)
                     p.Type.var_type)
              in
              { p with var_type })
        in
        OverloadMatching.signature context
          { call with call_decl = { call.call_decl with call_decl_formals = parameters } }
      in
      let* left_types = normalize left in
      let+ right_types = normalize right in
      List.equal Type.equal left_types right_types
      && List.for_all pairs ~f:(fun (left, right) ->
          Bool.equal left.var_ghost right.var_ghost
          && Bool.equal left.var_const right.var_const
          && Bool.equal left.var_implicit right.var_implicit)

let callable_target ~loc ~interface ~actual ~context ~instances (expected : Callable.t) =
  let open Rewriter.Syntax in
  let source = Callable.source_ident expected in
  let name = QualIdent.append actual source in
  let* projected = map_symbol interface actual (Module.CallDef expected) in
  let projected =
    match projected with
    | Module.CallDef call -> call
    | _ -> unsupported loc "invalid callable projection"
  in
  let* candidates = Rewriter.resolve_and_find_candidates name in
  let* matches =
    filter_map candidates ~f:(fun (name, symbol) ->
        let* symbol = Rewriter.Symbol.reify symbol in
        match symbol with
        | Module.CallDef call
          when Poly.equal (Callable.kind call) (Callable.kind expected) ->
            let* inputs =
              parameters_equal context instances projected
                projected.call_decl.call_decl_formals call.call_decl.call_decl_formals
            in
            let+ outputs =
              parameters_equal context instances projected
                projected.call_decl.call_decl_returns call.call_decl.call_decl_returns
            in
            Option.some_if (inputs && outputs) (name, call)
        | _ -> Rewriter.return None)
  in
  match matches with
  | [ match_ ] -> Rewriter.return match_
  | [] -> unsupported loc ("no compatible member " ^ Ident.to_string_user source)
  | _ -> unsupported loc ("ambiguous member " ^ Ident.to_string_user source)

let local ~loc declaration =
  {
    Stmt.stmt_loc = loc;
    stmt_desc =
      Basic (VarDef { var_decl = declaration; var_init = None; var_is_free = NotFree });
  }

let application ~loc name args = Expr.mk_app ~loc ~typ:Type.any (Expr.Var name) args

let builtin ~loc name args =
  application ~loc (QualIdent.from_ident (Ident.make loc name 0)) args

let forwarding_body ~loc ~self ~target (call : Callable.t) =
  let used =
    ref
      (Set.of_list
         (module Ident)
         (Callable.names ~stmt_ext_contents:(fun _ -> ([], [])) call))
  in
  let fresh stem =
    let rec choose index =
      let candidate = Ident.make loc stem index in
      if Set.mem !used candidate then choose (index + 1)
      else begin
        used := Set.add !used candidate;
        candidate
      end
    in
    choose 0
  in
  let declaration = call.call_decl in
  let atomic = Callable.is_atomic call.call_decl in
  let implicit = List.filter declaration.call_decl_formals ~f:(fun p -> p.var_implicit) in
  let opened =
    if not atomic then []
    else
      List.map implicit ~f:(fun p ->
          Type.mk_var_decl ~ghost:true ~loc (fresh "opened") p.var_type)
  in
  let _, args =
    List.fold_map declaration.call_decl_formals ~init:opened ~f:(fun remaining p ->
        if atomic && p.var_implicit then
          match remaining with
          | value :: remaining -> (remaining, Expr.from_var_decl value)
          | [] -> unsupported loc "invalid implicit parameter shape"
        else (remaining, Expr.from_var_decl p))
  in
  let returns = List.map declaration.call_decl_returns ~f:Expr.from_var_decl in
  let call_stmt =
    Stmt.mk_assign ~loc
      (List.map declaration.call_decl_returns ~f:(fun r ->
           QualIdent.from_ident r.var_name))
      (application ~loc target args)
  in
  let body =
    if not atomic then [ call_stmt ]
    else
      let token =
        Type.mk_var_decl ~ghost:true (fresh "token") (Type.mk_atomic_token loc self)
      in
      let token_value = Expr.from_var_decl token in
      [
        local ~loc token;
        Stmt.mk_assign ~loc
          [ QualIdent.from_ident token.var_name ]
          (builtin ~loc "bindAU" []);
      ]
      @ List.map opened ~f:(local ~loc)
      @ [
          Stmt.mk_assign ~loc
            (List.map opened ~f:(fun p -> QualIdent.from_ident p.var_name))
            (builtin ~loc "openAU" [ token_value ]);
          call_stmt;
          Stmt.mk_assign ~loc []
            (builtin ~loc "commitAU" [ token_value; Expr.mk_tuple ~loc returns ]);
        ]
  in
  Stmt.mk_block_stmt ~loc body

let module_ ~loc ~name ~interface ~actual =
  let open Rewriter.Syntax in
  let* interface, interface_symbol = Rewriter.resolve_and_find interface in
  let is_interface =
    match Rewriter.Symbol.orig_symbol interface_symbol with
    | Module.ModDef module_ -> module_.mod_decl.mod_decl_is_interface
    | Module.ModInst instance -> instance.mod_inst_is_interface
    | _ -> false
  in
  let* expected = Rewriter.Symbol.reify interface_symbol in
  let expected =
    match expected with
    | Module.ModDef module_ when is_interface -> module_
    | _ -> unsupported loc "the requested type is not an interface"
  in
  let* actual, actual_symbol = Rewriter.resolve_and_find actual in
  let* actual_module = Rewriter.Symbol.reify actual_symbol in
  let actual_module =
    match actual_module with
    | Module.ModDef module_
      when Module.is_structure module_.mod_decl
           && ((not module_.mod_decl.mod_decl_is_interface)
              || Rewriter.Symbol.is_module_instance actual_symbol) ->
        module_
    | _ -> unsupported loc "only instantiated structures can be adapted"
  in
  if not (Module.is_structure expected.mod_decl) then
    unsupported loc "the interface must be instantiated";
  let* projected_members =
    Rewriter.List.map expected.mod_def ~f:(function
      | Module.SymbolDef symbol ->
          let+ symbol = map_symbol interface actual symbol in
          Module.SymbolDef symbol
      | Module.Import directive -> Rewriter.return (Module.Import directive))
  in
  let own_symbols =
    List.filter_map actual_module.mod_def ~f:(function
      | Module.SymbolDef symbol -> Some (Symbol.to_name symbol, symbol)
      | Module.Import _ -> None)
    |> Map.of_alist_reduce (module Ident) ~f:(fun first _ -> first)
  in
  let context : OverloadMatching.context =
    {
      mod_qual_ident = actual;
      own_instrs = actual_module.mod_def;
      own_symbols;
      parent_instrs = projected_members;
    }
  in
  let* instances = OverloadMatching.match_instances context in
  let* scope = Rewriter.current_scope_id in
  let view = QualIdent.append scope name in
  let* members =
    filter_map expected.mod_def ~f:(function
      | Module.Import _ -> Rewriter.return None
      | Module.SymbolDef symbol -> (
          let member_name = Symbol.to_name symbol in
          let target = QualIdent.append actual member_name in
          let* mapped = map_symbol interface view symbol in
          match mapped with
          | Module.TypeDef definition ->
              let* target, target_symbol = Rewriter.resolve_and_find target in
              let* target_symbol = Rewriter.Symbol.reify target_symbol in
              begin match target_symbol with
              | Module.TypeDef _ -> ()
              | _ ->
                  unsupported loc
                    ("expected a type for " ^ Ident.to_string_user member_name)
              end;
              begin match definition.type_def_expr with
              | None ->
                  Rewriter.return
                    (Some
                       (Module.SymbolDef
                          (TypeDef
                             {
                               definition with
                               type_def_expr = Some (Type.mk_var ~loc target);
                               type_def_is_free = false;
                             })))
              | Some (Type.App (Data _, _, _)) ->
                  unsupported loc
                    "defined interface datatypes require an explicit adapter"
              | Some _ ->
                  let* projected = map_symbol interface actual symbol in
                  let expression =
                    match projected with
                    | Module.TypeDef { type_def_expr = Some expression; _ } -> expression
                    | _ -> unsupported loc "invalid type projection"
                  in
                  let* expression =
                    lift
                      (Rewriter.Type.rewrite_qual_idents
                         ~f:(OverloadMatching.rename_instance instances)
                         expression)
                  in
                  let* expression =
                    OverloadMatching.prepare_type context
                      (Set.empty (module QualIdent))
                      expression
                  in
                  let* required = TypeExpr.expand_type_expr expression in
                  let* provided = TypeExpr.expand_type_expr (Type.mk_var ~loc target) in
                  if has_token required || has_token provided then
                    unsupported loc "public atomic tokens require an explicit adapter";
                  if not (Type.equal required provided) then
                    unsupported loc
                      ("manifest type does not match " ^ Ident.to_string_user member_name);
                  Rewriter.return None
              end
          | Module.FieldDef field ->
              let* _, actual_field = Rewriter.resolve_and_find target in
              let* actual_field = Rewriter.Symbol.reify actual_field in
              let actual_field =
                match actual_field with
                | Module.FieldDef field -> field
                | _ ->
                    unsupported loc
                      ("expected a field for " ^ Ident.to_string_user member_name)
              in
              let expected_constraint =
                match symbol with
                | Module.FieldDef field ->
                    Option.map field.field_constraint ~f:(requalify interface actual)
                | _ -> None
              in
              let* constraints_agree =
                Interfaces.field_constraints_equal expected_constraint
                  actual_field.field_constraint
              in
              if not constraints_agree then unsupported loc "field constraints must agree";
              Rewriter.return
                (Some
                   (Module.SymbolDef
                      (FieldDef { field with field_alias = Some target; field_loc = loc })))
          | Module.VarDef variable ->
              if Option.is_some variable.var_init then
                unsupported loc "defined interface values are not supported";
              let* target = Rewriter.resolve_opt target in
              begin match target with
              | None when is_free variable.var_is_free -> Rewriter.return None
              | None ->
                  unsupported loc ("missing value " ^ Ident.to_string_user member_name)
              | Some target ->
                  let* actual_value = Rewriter.find_and_reify target in
                  begin match actual_value with
                  | Module.VarDef actual_value
                    when Bool.equal actual_value.var_decl.var_ghost
                           variable.var_decl.var_ghost ->
                      ()
                  | _ ->
                      unsupported loc
                        ("incompatible value " ^ Ident.to_string_user member_name)
                  end;
                  Rewriter.return
                    (Some
                       (Module.SymbolDef
                          (VarDef
                             {
                               variable with
                               var_init =
                                 Some (Expr.mk_var ~typ:variable.var_decl.var_type target);
                               var_is_free = NotFree;
                             })))
              end
          | Module.CallDef wanted ->
              if
                (not (Callable.is_abstract wanted))
                || wanted.call_decl.call_decl_is_sealed
              then
                unsupported loc "defined interface callables require an explicit adapter";
              if not (List.is_empty wanted.call_decl.call_decl_contract_ext) then
                unsupported loc "extension contracts are not supported";
              if
                List.exists
                  (wanted.call_decl.call_decl_formals @ wanted.call_decl.call_decl_returns)
                  ~f:(fun p -> has_token p.var_type)
              then unsupported loc "public atomic tokens require an explicit adapter";
              let* target, actual_call =
                callable_target ~loc ~interface ~actual ~context ~instances
                  (match symbol with Module.CallDef call -> call | _ -> wanted)
              in
              let () =
                if
                  not
                    (Bool.equal
                       (Callable.is_atomic wanted.call_decl)
                       (Callable.is_atomic actual_call.call_decl))
                then unsupported loc "ordinary and logically atomic contract kinds differ";
                if
                  wanted.call_decl.call_decl_physical_atomic
                  && not actual_call.call_decl.call_decl_physical_atomic
                then
                  unsupported loc
                    "an atomic proc requires a physically atomic actual procedure"
              in
              let formals =
                List.map2_exn wanted.call_decl.call_decl_formals
                  actual_call.call_decl.call_decl_formals ~f:(fun wanted actual ->
                    { wanted with Type.var_type = actual.Type.var_type })
              in
              let returns =
                List.map2_exn wanted.call_decl.call_decl_returns
                  actual_call.call_decl.call_decl_returns ~f:(fun wanted actual ->
                    { wanted with Type.var_type = actual.Type.var_type })
              in
              let declaration =
                {
                  wanted.call_decl with
                  call_decl_formals = formals;
                  call_decl_returns = returns;
                  call_decl_status = NotFree;
                  call_decl_is_sealed = false;
                  call_decl_alias = None;
                  call_decl_needs_mask = None;
                  call_decl_grants_mask = None;
                  call_decl_locals = [];
                  call_decl_loc = loc;
                }
              in
              let call = { wanted with call_decl = declaration } in
              let call =
                match Callable.kind call with
                | Pred | Invariant ->
                    if
                      not
                        (List.is_empty declaration.call_decl_precond
                        && List.is_empty declaration.call_decl_postcond)
                    then unsupported loc "resource aliases cannot carry contracts";
                    {
                      call with
                      call_decl =
                        {
                          declaration with
                          call_decl_alias = Some target;
                          call_decl_is_inline = false;
                          call_decl_is_auto = false;
                        };
                    }
                | Func ->
                    {
                      call with
                      call_def =
                        FuncDef
                          {
                            func_body =
                              Some
                                (application ~loc target
                                   (List.map declaration.call_decl_formals
                                      ~f:Expr.from_var_decl));
                          };
                    }
                | Proc | Lemma ->
                    {
                      call with
                      call_def =
                        ProcDef
                          {
                            proc_body =
                              Some
                                (forwarding_body ~loc
                                   ~self:
                                     (QualIdent.append view declaration.call_decl_name)
                                   ~target call);
                          };
                    }
              in
              let call =
                match Callable.kind call with
                | Pred | Invariant -> call
                | Proc | Lemma | Func ->
                    {
                      call with
                      call_decl =
                        {
                          call.call_decl with
                          call_decl_precond = [];
                          call_decl_postcond = [];
                          call_decl_opens = None;
                        };
                    }
              in
              Rewriter.return (Some (Module.SymbolDef (CallDef call)))
          | Module.ModInst instance when Option.is_none instance.mod_inst_def ->
              Rewriter.return
                (Some
                   (Module.SymbolDef
                      (ModInst
                         {
                           instance with
                           mod_inst_def = Some (Alias target);
                           mod_inst_is_checked = true;
                           mod_inst_is_free = false;
                           mod_inst_loc = loc;
                         })))
          | Module.ModInst _ -> Rewriter.return None
          | Module.ModDef definition
            when Poly.equal definition.mod_decl.mod_decl_status MachineFree ->
              Rewriter.return None
          | Module.ModDef _ ->
              unsupported loc "nested module definitions require an explicit adapter"
          | Module.ConstrDef _ | Module.DestrDef _ -> Rewriter.return None))
  in
  Rewriter.return
    Module.
      {
        mod_decl =
          {
            empty_decl with
            mod_decl_name = name;
            mod_decl_returns = [ (interface, []) ];
            mod_decl_loc = loc;
          };
        mod_def = members;
      }
