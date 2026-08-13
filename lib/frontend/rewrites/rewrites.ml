open Base
open Ast
open Util
open Frontend

let rec rewrite_stmt_error_msg call_id (stmt : Stmt.t) : Stmt.t Rewriter.t =
  match stmt.stmt_desc with
  | Basic (Spec (((Assert | Exhale) as kind), spec)) ->
      let error =
        ( Error.Verification,
          Expr.to_loc spec.spec_form,
          match kind with
          | Assert -> "This assertion may be violated"
          | _ -> "This assertion may not hold: insufficient permissions" )
      in
      let spec_error = spec.spec_error @ [Stmt.mk_const_spec_error error] in
      Rewriter.return
        { stmt with stmt_desc = Basic (Spec (kind, { spec with spec_error })) }
  | Loop loop_desc ->
      let loop_contract =
        List.map loop_desc.loop_contract ~f:(fun spec ->
            let error callee loc =
              ( Error.Verification,
                Expr.to_loc spec.spec_form,
                if Ident.(QualIdent.unqualify callee = call_id) then
                  "This loop invariant may not hold upon loop entry"
                else "This loop invariant may not be maintained" )
            in
            { spec with spec_error = [error] })
      in
      let stmt =
        { stmt with stmt_desc = Loop { loop_desc with loop_contract } }
      in
      Rewriter.Stmt.descend ~f:(rewrite_stmt_error_msg call_id) stmt
  | _ -> Rewriter.Stmt.descend ~f:(rewrite_stmt_error_msg call_id) stmt

let rewrite_callable_error_msg (call : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  let call_decl = call |> Callable.to_decl in
  let call_decl_postcond =
    List.map call_decl.call_decl_postcond ~f:(fun spec ->
        let error _ loc =
          Error.Verification,
          loc,
          "A postcondition may not hold at this return point"
        in
        (*let error_rel =
          ( Error.RelatedLoc,
            spec.spec_form |> Expr.to_loc,
            "This is the postcondition that may not hold" )
        in*)
        { spec with spec_error = spec.spec_error @ [error] })
  in
  let call_decl_precond =
    List.map call_decl.call_decl_precond ~f:(fun spec ->
        let error _ loc =
          Error.Verification,
          loc,
          "A precondition may not hold for this call"
        in
        (*let error_rel =
          ( Error.RelatedLoc,
            spec.spec_form |> Expr.to_loc,
            "This is the precondition that may not hold" )
        in*)
        { spec with spec_error = spec.spec_error @ [error] })
  in
  let call_decl = { call_decl with call_decl_postcond; call_decl_precond } in
  let+ call_def =
    match call.call_def with
    | ProcDef { proc_body = Some stmt } ->
        let+ body = rewrite_stmt_error_msg call_decl.call_decl_name stmt in
        Callable.ProcDef { proc_body = Some body }
    | _ -> Rewriter.return call.call_def
  in
  Callable.{ call_decl; call_def }

let rec rewrite_expand_types (tp_expr : type_expr) : type_expr Rewriter.t =
  Typing.ProcessTypeExpr.expand_type_expr tp_expr

let rec rewrite_inline_preds_expr seen (expr : expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | App (Var qual_ident, args, _) when not @@ Set.mem seen qual_ident -> begin
    let* symbol = Rewriter.find qual_ident in
    match Rewriter.Symbol.orig_symbol symbol with
    | CallDef { call_decl = { call_decl_kind = Pred; call_decl_is_auto = true; _ };
                call_def = FuncDef {func_body = Some _} } ->
      let* pred_def = Rewriter.find_and_reify_callable qual_ident in
      let pred_decl = pred_def.call_decl in
      let body = match pred_def.call_def with
        | FuncDef { func_body = Some body } -> body
        | _ -> assert false
      in
      let truncated_formal_args, dropped_formal_args =
        List.split_n (pred_decl.call_decl_formals @ pred_decl.call_decl_returns)
          (List.length args)
      in
      let loc = Expr.to_loc expr in
      let new_dropped_args =
        List.map dropped_formal_args ~f:(fun var_decl ->
            {
              var_decl with
              var_name =
                Ident.fresh loc var_decl.var_name.ident_name;
              var_loc = loc;
            })
      in
      
      let new_dropped_args_exprs =
        List.map new_dropped_args ~f:Expr.from_var_decl
      in
      let* _ =
        Rewriter.List.map new_dropped_args ~f:(fun var ->
            Rewriter.introduce_symbol
              (Module.VarDef { var_decl = var; var_init = None; var_is_free = NotFree }))
      in
      
      let new_renaming_map =
        List.fold2_exn
          (truncated_formal_args @ dropped_formal_args)
          (args @ new_dropped_args_exprs)
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map var_decl arg_expr ->
              Map.add_exn map
                ~key:(QualIdent.from_ident var_decl.var_name)
                ~data:arg_expr)
      in
      
      let new_body =
        Expr.mk_binder ~loc ~typ:(Expr.to_type expr) Exists new_dropped_args 
          (Expr.alpha_renaming body new_renaming_map)
      in
      rewrite_inline_preds_expr (Set.add seen qual_ident) new_body
    | _ -> Rewriter.Expr.descend expr ~f:(rewrite_inline_preds_expr seen)
  end
  | _ -> Rewriter.Expr.descend expr ~f:(rewrite_inline_preds_expr seen)


let rec rewrite_compr_expr (expr : expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | Binder (Compr, v_l, trgs, inner_expr, _expr_attr) ->
      let* _ = Rewriter.add_locals v_l
      and* inner_expr = rewrite_compr_expr inner_expr in

      let compr_fn_ident = Ident.fresh (Expr.to_loc expr) "compr" in

      let free_vars = Expr.signature inner_expr in
      let free_vars =
        Map.filter_keys free_vars ~f:(fun qual_ident ->
            not
              (List.exists v_l ~f:(fun v_l ->
                   QualIdent.(QualIdent.from_ident v_l.var_name = qual_ident))))
      in

      let formal_var_decls, actual_arg_exprs =
        Map.fold free_vars ~init:([], [])
          ~f:(fun ~key ~data (formals, actuals) ->
            if QualIdent.is_qualified key then (formals, actuals)
            else
              ( {
                  Type.var_name = QualIdent.unqualify key;
                  var_loc = Expr.to_loc inner_expr;
                  var_type = data;
                  var_const = true;
                  var_ghost = false;
                  var_implicit = false;
                }
                :: formals,
                Expr.set_loc (Expr.mk_var ~typ:data key) (Expr.to_loc inner_expr)
                :: actuals ))
      in

      let ret_var_decl =
        {
          Type.var_name = Ident.fresh (Expr.to_loc expr) "ret";
          var_loc = Expr.to_loc expr;
          var_type = Expr.to_type expr;
          var_const = false;
          var_ghost = false;
          var_implicit = false;
        }
      in

      let ret_typ = Expr.to_type expr in

      let postcond =
        let spec_form =
          (*if Type.is_set ret_typ then
            let var_decl = List.hd_exn v_l in

            Expr.mk_binder ~typ:Type.bool Forall [ var_decl ]
              (Expr.mk_and
                 [
                   Expr.mk_app ~typ:Type.bool Impl
                     [
                       inner_expr;
                       Expr.mk_app ~typ:Type.bool Elem
                         [
                           Expr.from_var_decl var_decl;
                           Expr.from_var_decl ret_var_decl;
                         ];
                     ];
                   Expr.mk_app ~typ:Type.bool Impl
                     [
                       Expr.mk_app ~typ:Type.bool Elem
                         [
                           Expr.from_var_decl var_decl;
                           Expr.from_var_decl ret_var_decl;
                         ];
                       inner_expr;
                     ];
                 ])
          else*)
            (* Type.is_map ret_typ *)
            let var_decl = List.hd_exn v_l in
            let lookup_expr =
              Expr.mk_app ~typ:(Type.map_codom ret_typ) MapLookUp
                [
                  Expr.from_var_decl ret_var_decl;
                  Expr.from_var_decl var_decl;
                ]
            in
            Expr.mk_binder ~typ:Type.bool ~trigs:[[lookup_expr]] Forall [ var_decl ]
              (Expr.mk_app ~typ:Type.bool Eq
                 [
                   inner_expr;
                   lookup_expr
                 ])
        in

        Stmt.mk_spec spec_form
      in

      let call_decl =
        {
          Callable.call_decl_kind = Func;
          call_decl_name = compr_fn_ident;
          call_decl_formals = formal_var_decls;
          call_decl_returns = [ ret_var_decl ];
          call_decl_locals = [];
          call_decl_precond = [];
          call_decl_postcond = [ postcond ];
          call_decl_contract_ext = [];
          call_decl_status = MachineFree;
          call_decl_is_auto = false;
          call_decl_needs_mask = None;
          call_decl_grants_mask = None;
          call_decl_loc = Expr.to_loc expr;
               call_decl_loc_params = [];
        }
      in

      let* current_module_name = Rewriter.current_module_name in
      let compr_fn_qual_ident =
        QualIdent.append current_module_name compr_fn_ident
      in
      let compr_fn_def =
        Module.CallDef
          Callable.{ call_decl; call_def = FuncDef { func_body = None } }
      in

      let* () = Rewriter.Logs.debug (fun printers m ->
          m "Rewrites.rewrite_compr_expr: compr_fn: %a" printers.pr_symbol compr_fn_def) in

      let new_expr =
        Expr.mk_app ~typ:ret_typ ~loc:(Expr.to_loc expr)
          (Expr.Var compr_fn_qual_ident) actual_arg_exprs
      in

      (* TODO: Change Rewriter.introduce_symbol to Rewriter.introduce_typecheck_symbol *)
      let+ _ = Rewriter.introduce_symbol compr_fn_def in
      new_expr
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_compr_expr

(* Shared by [rewrite_set_diff_and_choose_expr]'s [Diff] and [Choose] cases: both
   desugar to a call to a synthesized, axiomatized (`MachineFree`, no body)
   function, differing only in arity, postcondition shape, and -- critically --
   [fn_ident]: [Diff]'s caller passes a fresh one per source occurrence (matching
   this rewrite's original, [Diff]-only behavior: two `--` occurrences never need
   to agree on anything beyond their own postcondition), but [Choose]'s caller
   passes a *deterministic* one and only calls this once per (module, element
   type) pair -- every other occurrence reuses the qual_ident its caller already
   found via [Rewriter.resolve_opt] instead of calling this again. `choose`
   has to be deduplicated this way: unlike `--`, whose result is fully determined
   by its own two operands, two *different* synthesized functions both claiming
   "some unspecified member of s" would be free to disagree with each other on
   the same s, breaking the (needed, e.g. by SetOrder's embed below) assumption
   that `choose(s)` consistently names the same element everywhere it's written.
   Builds the [call_decl], introduces and type-checks it in the current module
   via [Rewriter.introduce_typecheck_symbol] (TODO: switch to
   [Rewriter.introduce_typecheck_symbol] proper once it exists for symbols that
   aren't types -- see the original comment this carries forward), and returns
   the call expression invoking it with [actual_arg_exprs]. *)
let introduce_synthesized_set_op_fn ~(loc : location) ~(fn_ident : ident)
    ~(formal_var_decls : var_decl list)
    ~(actual_arg_exprs : expr list) ~(ret_var_decl : var_decl)
    ~(postcond_spec_form : expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  let ret_typ = ret_var_decl.Type.var_type in
  let call_decl =
    {
      Callable.call_decl_kind = Func;
      call_decl_name = fn_ident;
      call_decl_formals = formal_var_decls;
      call_decl_returns = [ ret_var_decl ];
      call_decl_locals = [];
      call_decl_precond = [];
      call_decl_postcond = [ Stmt.mk_spec postcond_spec_form ];
      call_decl_contract_ext = [];
      call_decl_status = MachineFree;
      call_decl_is_auto = false;
      call_decl_needs_mask = None;
      call_decl_grants_mask = None;
      call_decl_loc = loc;
               call_decl_loc_params = [];
    }
  in

  let* current_module_name = Rewriter.current_module_name in

  let fn_qual_ident = QualIdent.append current_module_name fn_ident in
  let fn_def =
    Module.CallDef Callable.{ call_decl; call_def = FuncDef { func_body = None } }
  in

  let new_expr =
    Expr.mk_app ~typ:ret_typ ~loc (Expr.Var fn_qual_ident) actual_arg_exprs
  in

  (* TODO: Change Rewriter.introduce_symbol to Rewriter.introduce_typecheck_symbol *)
  let+ _ =
    Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.process_symbol fn_def
  in
  new_expr

let mk_fresh_var_decl loc name var_type =
  {
    Type.var_name = Ident.fresh loc name;
    var_loc = loc;
    var_type;
    var_const = true;
    var_ghost = false;
    var_implicit = false;
  }

let rec rewrite_set_diff_and_choose_expr (expr : expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | App (Diff, [ expr1; expr2 ], _expr_attr) ->
      let* () = Rewriter.Logs.debug (fun printers m ->
          m "Rewrites.rewrite_set_diff_and_choose_expr: expr: %a" printers.pr_expr expr) in

      let* expr1 = rewrite_set_diff_and_choose_expr expr1 in
      let* expr2 = rewrite_set_diff_and_choose_expr expr2 in

      let loc = Expr.to_loc expr in
      let set_element_type = Type.set_elem (Expr.to_type expr1) in
      let typ_string = ProgUtils.serialize (Type.to_string set_element_type) in
      let fn_ident = Ident.fresh loc (Stdlib.Format.asprintf "set_diff$%s" typ_string) in
      let var_decl1 = mk_fresh_var_decl loc "a" (Expr.to_type expr1) in
      let var_decl2 = mk_fresh_var_decl loc "b" (Expr.to_type expr1) in
      let ret_var_decl = { (mk_fresh_var_decl loc "ret" (Expr.to_type expr)) with var_const = false } in

      let postcond_spec_form =
        let var_decl = mk_fresh_var_decl loc "x" set_element_type in
        let elem_of vd1 vd2 =
          Expr.mk_app ~typ:Type.bool Elem [ Expr.from_var_decl vd1; Expr.from_var_decl vd2 ]
        in
        Expr.mk_binder ~typ:Type.bool Forall [ var_decl ]
          ((* forall x :: *)
           Expr.mk_and
             [
               Expr.mk_app ~typ:Type.bool Impl
                 [
                   (*    x \in a && !(x \in b)   ==>    x \in ret  *)
                   Expr.mk_and
                     [ elem_of var_decl var_decl1; Expr.mk_not (elem_of var_decl var_decl2) ];
                   elem_of var_decl ret_var_decl;
                 ];
               Expr.mk_app ~typ:Type.bool Impl
                 [
                   (*    x \in ret    ==>    x \in a && !(x \in b)  *)
                   elem_of var_decl ret_var_decl;
                   Expr.mk_and
                     [ elem_of var_decl var_decl1; Expr.mk_not (elem_of var_decl var_decl2) ];
                 ];
             ])
      in
      introduce_synthesized_set_op_fn ~loc ~fn_ident
        ~formal_var_decls:[ var_decl1; var_decl2 ] ~actual_arg_exprs:[ expr1; expr2 ]
        ~ret_var_decl ~postcond_spec_form
  | App (Choose, [ expr1 ], _expr_attr) ->
      let* () = Rewriter.Logs.debug (fun printers m ->
          m "Rewrites.rewrite_set_diff_and_choose_expr: expr: %a" printers.pr_expr expr) in

      let* expr1 = rewrite_set_diff_and_choose_expr expr1 in

      let loc = Expr.to_loc expr in
      let set_element_type = Expr.to_type expr in
      let typ_string = ProgUtils.serialize (Type.to_string set_element_type) in
      (* Deterministic, not [Ident.fresh]: see [introduce_synthesized_set_op_fn]'s
         doc comment for why every [choose] occurrence for a given element type,
         within a module, has to resolve to the very same function. *)
      let fn_ident = Ident.make loc (Stdlib.Format.asprintf "choose$%s" typ_string) 0 in
      let* current_module_name = Rewriter.current_module_name in
      let fn_qual_ident = QualIdent.append current_module_name fn_ident in
      let* existing = Rewriter.resolve_opt fn_qual_ident in
      (match existing with
       | Some qi -> Rewriter.return (Expr.mk_app ~typ:set_element_type ~loc (Expr.Var qi) [ expr1 ])
       | None ->
         (* The formal is `Set[T]`, not `expr1`'s own (possibly `FinSet[T]`) type:
            `choose` works on `FinSet[T]` contravariantly, via the same upcast any
            other call with a wider-typed formal gets, so this one synthesized
            function per element type serves both. *)
         let set_type = Type.set_typed set_element_type in
         let var_decl_s = mk_fresh_var_decl loc "s" set_type in
         let ret_var_decl = { (mk_fresh_var_decl loc "res" set_element_type) with var_const = false } in
         let postcond_spec_form =
           (*    s != {||}   ==>   res \in s  *)
           Expr.mk_impl
             (Expr.mk_not (Expr.mk_eq (Expr.from_var_decl var_decl_s) (Expr.mk_app ~typ:set_type Empty [])))
             (Expr.mk_app ~typ:Type.bool Elem
                [ Expr.from_var_decl ret_var_decl; Expr.from_var_decl var_decl_s ])
         in
         introduce_synthesized_set_op_fn ~loc ~fn_ident
           ~formal_var_decls:[ var_decl_s ] ~actual_arg_exprs:[ expr1 ]
           ~ret_var_decl ~postcond_spec_form)
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_set_diff_and_choose_expr

let rewrite_compr_modules (tbl : SymbolTbl.t) (m : Module.t) =
  Rewriter.eval
    (Rewriter.Module.rewrite_expressions ~f:rewrite_compr_expr m)
    tbl

(** Rewrites loops into recursive function calls. For example, if we have the following while loop:
  ```
    proc p() {
      ...
      while(c)
        inv i
      {
        x = y + z
      }
      ...
    }
  ```

  Then we rewrite it into the following, by defining a recursive function:
  ```
    proc p() {
      ...
      x = p_loop(x, y, z);
      ...
    }

    proc p_loop(x1: Int, y1: Int, z1: Int)
      returns x2
      requires i[x1\x, y1\y, z1\z]
      ensures i[x2\x, y1\y, z1\z]
      ensures !c[x2\x, y1\y, z1\z]
    {
      x2 := x1
      
      if(c[x1\x, y1\y, z1\z]) {
        x1 := y1 + z1;
        
        x2 := p_loop(x1, y1, z1);
      } else { 
      }

      return x2
    }
  ```
*)

(** `--strict` diagnostics never fire inside the standard library (core or
    extension-supplied): it's not the user's code to annotate, and its declarations
    don't even have a real path on disk to print a source excerpt from ([Loc.context]
    only special-cases the core [Library.sources] strings, not extension [lib_sources]
    files like `well_founded_order.rav`). *)
let is_library_qual_ident (qid : QualIdent.t) : bool =
  String.(Ident.name (QualIdent.first_ident qid) = Ident.name Predefs.lib_ident)

let rec rewrite_loops (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Loop loop ->
      let* loop_prebody = rewrite_loops loop.loop_prebody in
      let* loop_postbody = rewrite_loops loop.loop_postbody in
      let loop = { loop with loop_prebody; loop_postbody } in
      let loc = Stmt.to_loc stmt in
      let* () = Rewriter.Logs.debug (fun printers m -> m "Rewrites.rewrite_loops: loop: %a" printers.pr_stmt stmt) in

      let* ( loop_arg_var_decls,
             loop_arg_renaming_map,
             loop_arg_renaming_qual_ident_map,
             curr_loop_arg_var_decls ) =
        (* Local variables accessed from loop body become arguments for loop procedure *)
        let curr_loop_args =
          List.fold ~init:(Set.empty (module Ident)) 
          ~f:Set.union
            (
              (Stmt.local_vars_accessed loop.loop_postbody) ::
              (Expr.local_vars loop.loop_test) ::
              (List.map ~f:(fun s -> Expr.local_vars s.spec_form) loop.loop_contract)
            )
            
          |> Set.to_list
        in
        let+ curr_loop_arg_var_decls =
          Rewriter.List.map curr_loop_args ~f:(fun var ->
              let+ symbol =
                Rewriter.find_and_reify (QualIdent.from_ident var)
              in

              match symbol with
              | VarDef v -> v.var_decl
              | _ ->
                  Error.internal_error stmt.stmt_loc
                    ("expected a variable; found " ^ Symbol.to_string symbol
                   ^ " for var: " ^ Ident.to_string var))
        in

        (* redefined loop_args for uniqueness *)
        let loop_arg_var_decls =
          List.map curr_loop_arg_var_decls ~f:(fun var_decl ->
              let new_var_name =
                Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name
              in
              Logs.debug (fun m ->
                  m "Loop old_var_name: %a" Ident.pr var_decl.var_name);
              Logs.debug (fun m ->
                  m "Loop new_var_name: %a" Ident.pr new_var_name);
              let new_new_var_name =
                Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name
              in
              Logs.debug (fun m ->
                  m "Loop new_new_var_name: %a" Ident.pr new_new_var_name);
              { var_decl with var_name = new_var_name }
              (* { var_decl with var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name } *))
        in

        Logs.debug (fun m ->
            m "Loop curr_loop_arg_var_decls:\n %a"
              (Print.pr_list_comma Ident.pr)
              (List.map curr_loop_arg_var_decls ~f:(fun var_decl ->
                   var_decl.var_name)));

        Logs.debug (fun m ->
            m "Loop loop_arg_var_decls:\n %a"
              (Print.pr_list_comma Ident.pr)
              (List.map loop_arg_var_decls ~f:(fun var_decl ->
                   var_decl.var_name)));

        let loop_arg_renaming_map =
          List.fold2_exn curr_loop_arg_var_decls loop_arg_var_decls
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map old_var_decl new_var_decl ->
              Map.add_exn map
                ~key:(QualIdent.from_ident old_var_decl.var_name)
                ~data:(Expr.from_var_decl new_var_decl))
        in

        let loop_arg_renaming_qual_ident_map =
          List.fold2_exn curr_loop_arg_var_decls loop_arg_var_decls
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map old_var_decl new_var_decl ->
              Map.add_exn map
                ~key:(QualIdent.from_ident old_var_decl.var_name)
                ~data:(QualIdent.from_ident new_var_decl.var_name))
        in

        ( loop_arg_var_decls,
          loop_arg_renaming_map,
          loop_arg_renaming_qual_ident_map,
          curr_loop_arg_var_decls )
      in

      let* loop_ret_var_decls, loop_ret_renaming_map, curr_loop_ret_var_decls, loop_local_var_decls =
        (* Local variables modified from loop body become ret vals for loop procedure *)
        let* ext_hooks = Rewriter.current_ext_hooks in
        let curr_loop_rets =
          Stmt.make_stmt_local_vars_modified
            ~basic_stmt_ext_local_vars_modified:ext_hooks.basic_stmt_ext_local_vars_modified
            ~stmt_ext_local_vars_modified:ext_hooks.stmt_ext_local_vars_modified
            loop.loop_postbody
        in
        let* curr_loop_ret_var_decls =
          Rewriter.List.map curr_loop_rets ~f:(fun var ->
            let+ var_def = Rewriter.find_and_reify_var (QualIdent.from_ident var) in
            var_def.var_decl
          )
        in

        (* redefined loop_rets for uniqueness *)
        let loop_ret_var_decls =
          List.map curr_loop_ret_var_decls ~f:(fun var_decl ->
              {
                var_decl with
                var_name =
                  Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
              })
        in

        let loop_ret_renaming_map =
          List.fold2_exn curr_loop_ret_var_decls loop_ret_var_decls
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map old_var_decl new_var_decl ->
              Map.add_exn map
                ~key:(QualIdent.from_ident old_var_decl.var_name)
                ~data:(Expr.from_var_decl new_var_decl))
        in

        let loop_local_vars = Stmt.stmt_local_vars_initialized loop.loop_postbody in
        let+ loop_local_var_decls =
          Rewriter.List.map loop_local_vars ~f:(fun var ->
            let+ var_def = Rewriter.find_and_reify_var (QualIdent.from_ident var) in
            var_def.var_decl
          )

        in

        (loop_ret_var_decls, loop_ret_renaming_map, curr_loop_ret_var_decls, loop_local_var_decls)
      in

      (* A loop's synthesized callable is a [Lemma] iff the loop itself is in a
         ghost scope (which also covers a loop inside an enclosing [Lemma]).
         [Rewriter.enter]'s ghost-scope check looks only at the newly-entered
         callable's own kind, not the context it was introduced in, so a
         [Proc] synthesized from a loop inside ghost code would type-check
         with ghost-scope off and reject the ghost state the loop touches. *)
      let* loop_proc_name, is_ghost_scope =
        let* proc_name = Rewriter.current_scope_id in
        let+ is_ghost_scope = Rewriter.is_ghost_scope in
        ( Ident.fresh stmt.stmt_loc (proc_name.qual_base.ident_name ^ "_loop"),
          is_ghost_scope )
      in

      (* Create new map which replaces loop_arg vars with loop_ret vars, for post conditions *)
      let loop_post_vars_renaming_map =
        Map.fold loop_ret_renaming_map ~init:loop_arg_renaming_map
          ~f:(fun ~key ~data map -> Map.set map ~key ~data)
      in

      let* ext_hooks = Rewriter.current_ext_hooks in

      let new_proc_decl =
        let loop_precond =
          List.map loop.loop_contract ~f:(fun spec ->
              {
                spec with
                spec_form =
                  Expr.alpha_renaming spec.spec_form loop_arg_renaming_map;
              })
        in

        let loop_postcond =
          List.map loop.loop_contract ~f:(fun spec ->
              {
                spec with
                spec_form =
                  Expr.alpha_renaming spec.spec_form loop_post_vars_renaming_map;
              })
        in

        (* Adding negation of loop_cond to postconditions *)
        let loop_postcond =
          loop_postcond
          @ [
              Stmt.mk_spec
                (Expr.mk_not ~loc:stmt.stmt_loc
                   (Expr.alpha_renaming loop.loop_test
                      loop_post_vars_renaming_map));
            ]
        in

        (* Transfer the loop's own decreases (or other contract-extension) clauses onto
           the synthesized recursive procedure the same way loop_contract is transferred
           above: once here, the generic recursive-call instrumentation pass picks up
           [call_decl_contract_ext] uniformly, so loop termination checking needs no
           separate code path -- see WISHLIST.md, "decreases clauses", Phase 1.
           [rewrite_contract_ext_loop_transfer] applies the same substitution used for
           [loop_contract] above and lets an extension swap in loop-specific wording
           (e.g. via a payload built on [Stmt.spec], whose [spec_error] the extension
           can override) -- without this code needing to know what any [contract_ext]
           value means. *)
        let loop_contract_ext =
          List.map loop.loop_contract_ext
            ~f:(ext_hooks.rewrite_contract_ext_loop_transfer
                  ~subst:(fun e -> Expr.alpha_renaming e loop_arg_renaming_map))
        in

        {
          Callable.call_decl_kind = (if is_ghost_scope then Lemma else Proc);
          call_decl_name = loop_proc_name;
          call_decl_formals = loop_arg_var_decls;
          call_decl_returns = loop_ret_var_decls;
          call_decl_locals = loop_local_var_decls;
          call_decl_precond = loop_precond;
          call_decl_postcond = loop_postcond;
          call_decl_contract_ext = loop_contract_ext;
          call_decl_status = NotFree;
          call_decl_is_auto = false;
          call_decl_needs_mask = None;
          call_decl_grants_mask = None;
          call_decl_loc = stmt.stmt_loc;
               call_decl_loc_params = [];
        }
      in

      let* loop_body =
        let set_ret_vals_to_initial_args =
          List.map (Map.to_alist loop_ret_renaming_map)
            ~f:(fun (old_var, new_expr) ->
              Stmt.mk_assign ~loc [ new_expr |> Expr.to_qual_ident ]
                (Map.find_exn loop_arg_renaming_map old_var))
        in

        let recurse_call =
          let lhs_list =
            List.map loop_ret_var_decls ~f:(fun var_decl ->
                QualIdent.from_ident var_decl.var_name)
          in

          let args_list =
            List.map loop_arg_var_decls ~f:(fun var_decl ->
                Expr.from_var_decl var_decl)
          in

          Stmt.mk_call ~loc ~lhs:lhs_list
            (QualIdent.from_ident loop_proc_name)
            args_list ~is_spawn:false
        in

        (* TODO: Rename variables from curr_vars to loop_vars in loop body *)
        let* loop_body =
          Rewriter.Stmt.rewrite_qual_idents loop.loop_postbody
            ~f:(fun qual_ident ->
              Option.value
                (Map.find loop_arg_renaming_qual_ident_map qual_ident)
                ~default:qual_ident)
        in

        let cond_stmt =
          let test =
            Some (Expr.alpha_renaming loop.loop_test loop_arg_renaming_map)
          in
          let then_stmt = Stmt.mk_block_stmt ~loc [ loop_body; recurse_call ] in
          let else_stmt = Stmt.mk_skip ~loc in

          Stmt.mk_cond ~loc test then_stmt else_stmt
        in

        let ret_stmt =
          let ret_tuple =
            Expr.mk_tuple ~loc:stmt.stmt_loc
              (List.map loop_ret_var_decls ~f:(fun var_decl ->
                   Expr.from_var_decl var_decl))
          in

          Stmt.mk_return ~loc:stmt.stmt_loc ret_tuple
        in

        Rewriter.return
          (Stmt.mk_block_stmt ~loc:stmt.stmt_loc
             (set_ret_vals_to_initial_args @ [ cond_stmt; ret_stmt ]))
      in

      let loop_proc_symbol =
        let call_def =
          Callable.
            {
              call_decl = new_proc_decl;
              call_def = ProcDef { proc_body = Some loop_body };
            }
        in
        Module.CallDef call_def
      in

      let* () = Rewriter.Logs.debug (fun printers m ->
          m "Rewrites.rewrite_loops: Pre-typecheck loop_proc_symbol:\n %a"
            printers.pr_symbol loop_proc_symbol) in

      let* _ =
        Rewriter.introduce_typecheck_symbol ~loc:stmt.stmt_loc
          ~f:Typing.process_symbol loop_proc_symbol
      in

      let* curr_state = Rewriter.__get_state in

      (* Logs.debug (fun m ->
          let open Rewriter in
          m "Rewrites.rewrite_loops: Loop curr_scope:\n %a" QualIdent.pr
            curr_state.state_table.tbl_curr.scope_id); *)

      let new_stmt =
        let lhs_list =
          List.map curr_loop_ret_var_decls ~f:(fun var_decl ->
              QualIdent.from_ident var_decl.var_name)
        in
        let args_list =
          List.map curr_loop_arg_var_decls ~f:(fun var_decl ->
              Expr.from_var_decl var_decl)
        in

        (* Stmt.mk_call ~loc ~lhs:lhs_list
          (QualIdent.from_ident loop_proc_name)
          args_list ~is_spawn:false *)

        Stmt.mk_cond ~loc (Some loop.loop_test) 
          (Stmt.mk_call ~loc ~lhs:lhs_list
            (QualIdent.from_ident loop_proc_name) args_list ~is_spawn:false
          ) (Stmt.mk_skip ~loc)
      in

      let* () = Rewriter.Logs.debug (fun printers m -> m "Loop new_stmt:\n %a" printers.pr_stmt new_stmt) in
      Rewriter.return new_stmt
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_loops

let rec rewrite_ret_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Return ret_expr) ->
      let loc = Stmt.to_loc stmt in

      let* curr_proc_name = Rewriter.current_scope_id in

      let* callable_decl =
        Logs.debug (fun m ->
            m "Rewrites.rewrite_ret_stmts: curr_proc_name: %a" QualIdent.pr
              curr_proc_name);

        Rewriter.find_and_reify_callable curr_proc_name |+> fun c -> c.call_decl
      in

      let ret_expr_list = Expr.unfold_tuple ret_expr in

      let truncated_returns, dropped_returns =
        List.split_n callable_decl.call_decl_returns
          (List.length ret_expr_list)
      in

      (*let fresh_dropped_returns =
        List.map dropped_formal_args ~f:(fun var_decl ->
            {
              var_decl with
              var_name =
                Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
              var_loc = stmt.stmt_loc;
            })
      in*)

      let dropped_returns_exprs =
        List.map dropped_returns ~f:Expr.from_var_decl
      in

      let dropped_returns_vars =
        List.map dropped_returns ~f:(fun decl -> QualIdent.from_ident decl.var_name)
      in
      
      let ret_expr = Expr.mk_tuple (ret_expr_list @ dropped_returns_exprs) in
      
      (* Need to ensure that call_decl_returns and call_desc.call_lhs line up *)
      let renaming_map =
        List.fold2_exn
          callable_decl.call_decl_returns
          (ret_expr_list @ dropped_returns_exprs)
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map var_decl arg_expr ->
              Map.add_exn map
                ~key:(QualIdent.from_ident var_decl.var_name)
                ~data:arg_expr)
      in

      (*let renaming_map =
        List.fold2_exn callable_decl.call_decl_returns ret_expr_list
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map var_decl expr ->
            Map.add_exn map
              ~key:(QualIdent.from_ident var_decl.var_name)
              ~data:expr)
      in*)

      let postconds_spec = callable_decl.call_decl_postcond in

      let postcond, spec_error =
        if Callable.is_atomic callable_decl then
          let atomic_token_var =
            Expr.mk_var ~typ:(Type.atomic_token curr_proc_name)
              (QualIdent.from_ident
                 (ProgUtils.callable_au_token_ident ~loc
                    callable_decl.call_decl_name))
          in

          let concrete_args =
            List.filter callable_decl.call_decl_formals ~f:(fun var_decl ->
                not var_decl.var_implicit)
          in
          let concrete_args_expr =
            List.map concrete_args ~f:Expr.from_var_decl
          in

          let error =
            ( Error.Verification,
              loc,
              "The atomic specification may not have been committed before \
               reaching this return point" )
          in
          [Expr.mk_app ~loc ~typ:Type.perm
            (Expr.AUPredCommit curr_proc_name)
            ([atomic_token_var; Expr.mk_tuple concrete_args_expr;  ret_expr ])],
          [ Stmt.mk_const_spec_error error ]
        else
          List.map postconds_spec ~f:(fun spec ->
              Expr.alpha_renaming spec.spec_form renaming_map),
          let error =
            ( Error.Verification,
              loc,
              "A postcondition may not hold at this return point" )
          in
          [ Stmt.mk_const_spec_error error ]
      in
      
      let bind_stmt =
        match dropped_returns with
        | [] -> Stmt.mk_skip ~loc
        | _ ->
          Stmt.mk_bind ~loc dropped_returns_vars
            (Stmt.mk_spec
               ~atomic:false
               ~cmnt:("bind added for return stmt: " ^ Stmt.to_string stmt)
               ~spec_error
               (Expr.mk_and postcond))
      in
        
      let postconds_exhale_stmts =
        List.map postcond ~f:(fun expr ->
            Stmt.mk_exhale_expr ~cmnt:("exhape added for return stmt: " ^ Stmt.to_string stmt) ~loc
              ~spec_error
              expr)
      in

      let assume_false =
        Stmt.mk_assume_expr ~loc:stmt.stmt_loc
          (Expr.mk_bool ~loc:stmt.stmt_loc false)
      in

      let new_stmt =
        Stmt.mk_block_stmt ~loc:stmt.stmt_loc
          (bind_stmt :: postconds_exhale_stmts @ [ assume_false ])
      in

      Rewriter.return new_stmt
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_ret_stmts

(** Runs once per [Proc]/[Lemma] callable, before [rewrite_contract_ext_calls]
    below visits any of its statements: delegates to [ext_hooks.rewrite_callable_entry]
    to (possibly) prepend statements at the top of the body -- e.g. ghost locals
    snapshotting a decreases measure's entry-time value, needed because the
    callable's own formals may be reassigned by the body before a recursive call is
    reached. General-purpose, not tied to [contract_ext] at all (see
    [ExtApi.Ext.rewrite_callable_entry]'s doc comment), so this runs unconditionally
    for every [Proc]/[Lemma] rather than gating on [call_decl_contract_ext]; it's up
    to each extension's own implementation to decide whether it has anything to do
    for a given callable, and the default is to prepend nothing. *)
let rewrite_callable_entries (callable : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match callable.call_decl.call_decl_kind, callable.call_def with
  | (Proc | Lemma), ProcDef { proc_body = Some body } ->
    let* ext_hooks = Rewriter.current_ext_hooks in
    let+ prepend_stmts = ext_hooks.rewrite_callable_entry callable.call_decl in
    (match prepend_stmts with
     | [] -> callable
     | _ ->
       let new_body =
         Stmt.mk_block_stmt ~loc:callable.call_decl.call_decl_loc (prepend_stmts @ [ body ])
       in
       { callable with call_def = ProcDef { proc_body = Some new_body } })
  | _ -> Rewriter.return callable

(** The module's call graph, decomposed into strongly-connected components, computed
    once per module (see [build_scc_map]) right after [rewrite_loops] so synthesized
    tail-recursive loop-procs are graph vertices too. [sccs] is every component (in
    [CallGraph.Graph.topsort] order); [scc_id_of] maps each vertex to its component's
    index into [sccs], for a cheap "are these two in the same recursive group" check
    ([same_scc] below). A self-recursive callable with no other mutual dependencies is
    exactly a singleton component with a self-loop -- [CallGraph.Graph.topsort]
    doesn't merge it with anything else, so this subsumes Phase 1's plain
    self-recursion check as the size-1 case, with no special-casing needed. *)
type scc_map = {
  sccs : QualIdent.t list list;
  scc_id_of : int qual_ident_map;
  self_loops : QualIdentSet.t;  (** vertices with an edge to themselves *)
}

let build_scc_map (tbl : SymbolTbl.t) (m : Module.t) : scc_map =
  let g = CallGraph.build tbl m in
  let sccs = CallGraph.Graph.topsort g in
  let scc_id_of =
    List.concat_mapi sccs ~f:(fun i members -> List.map members ~f:(fun v -> (v, i)))
    |> Map.of_alist_exn (module QualIdent)
  in
  let self_loops =
    Set.filter (CallGraph.Graph.vertices g) ~f:(fun v -> Set.mem (CallGraph.Graph.succs g v) v)
  in
  { sccs; scc_id_of; self_loops }

let same_scc (sm : scc_map) (a : QualIdent.t) (b : QualIdent.t) : bool =
  match Map.find sm.scc_id_of a, Map.find sm.scc_id_of b with
  | Some ia, Some ib -> Int.equal ia ib
  | _ -> false

(** Runs once per module, after [build_scc_map] and before any per-callable pass below,
    for every strongly-connected component that's actually recursive -- a self-loop
    singleton, or any >1-member (mutually-recursive) group -- delegating to
    [ext_hooks.check_contract_ext_group_compatible] with the resolved [call_decl]s.
    Core doesn't know what "compatible" means for any given [contract_ext]; it only
    knows this component is recursive, which is exactly the shape a whole-group check
    (as opposed to [type_check_contract_ext]'s single-callable view) needs --
    [DecreasesExt] uses it both for its cross-member mixed-coverage/arity/instance
    checks (which no-op harmlessly when there's only one resolved member, so a
    self-loop singleton costs it nothing extra to handle) and, under `--strict`, for
    its missing-`decreases` diagnostic (self- or mutually-recursive alike -- see
    [rewrite_loops], which gives a loop's synthesized tail-recursive callable the same
    kind as whatever callable the loop came from, so a loop is just another
    self-recursive vertex here, no separate handling needed). A component can contain
    non-callable vertices too (e.g. two mutually-recursive `data` type definitions --
    [CallGraph.build] graphs every top-level symbol, not just callables), and members
    rooted in the standard library (core or extension-supplied) are dropped before
    resolution -- diagnosing library internals isn't this hook's job, and library
    declarations don't have a real path on disk for [Loc.context] to print an excerpt
    from. Each lookup uses [SymbolTbl.goto] against the plain (non-monadic) [tbl]
    snapshot the SCC map was built from, then a throwaway, non-state-updating
    [Rewriter.eval] -- exactly how [Dependencies.analyze]'s [inst_dependencies]
    (lib/backend/dependencies.ml) already resolves arbitrary graph-vertex idents found
    outside the scope that's "current" in the ambient traversal, since [Rewriter.find]
    resolves names relative to whatever scope is current, not as absolute paths. *)
let check_contract_ext_group_compatibility (tbl : SymbolTbl.t) (sm : scc_map) : unit Rewriter.t =
  let open Rewriter.Syntax in
  let resolve_call_decls members =
    List.filter_map members ~f:(fun qid ->
        if is_library_qual_ident qid then None
        else
          let tbl1 = SymbolTbl.goto qid tbl in
          let _, symbol = Rewriter.eval ~update:false (Rewriter.find_and_reify qid) tbl1 in
          match symbol with
          | Module.CallDef call_def -> Some call_def.Callable.call_decl
          | _ -> None)
  in
  Rewriter.List.iter sm.sccs ~f:(fun members ->
      let is_recursive =
        match members with
        | [] -> false
        | [ qid ] -> Set.mem sm.self_loops qid
        | _ -> true
      in
      if not is_recursive then Rewriter.return ()
      else
        match resolve_call_decls members with
        | [] -> Rewriter.return ()
        | call_decls ->
          let* ext_hooks = Rewriter.current_ext_hooks in
          ext_hooks.check_contract_ext_group_compatible call_decls)

(** For every call in a [Proc]/[Lemma] body whose *callee* has a non-empty
    [call_decl_contract_ext], delegates to [ext_hooks.rewrite_contract_ext_call] to
    (possibly) insert statements (e.g. a decreases progress-check assert) immediately
    before the call. Core code here doesn't know what [call_decl_contract_ext] means --
    it only knows that any non-empty payload means some extension may want to
    instrument this call site; the per-call [call_decl_contract_ext <> []] check keeps
    this a no-op (beyond one symbol lookup) for the overwhelming majority of calls,
    whose callee has no contract-extension clauses at all.

    Note this is *not* restricted to self-recursive calls: any call to any callable
    carrying a contract-extension clause is offered to the hook, caller and callee
    identity included, along with whether they lie in the same strongly-connected
    component of [sm] (self- or mutually-recursive alike), so an extension can filter
    down to whatever notion of "recursive"/"relevant" it needs (e.g. [DecreasesExt]
    only acts when that's [true]) without core needing to know what that notion is.
    This also means a future contract extension whose calls don't need to be
    recursive at all -- e.g. something that must hold at *every* call to a given
    callable -- doesn't need a different pass.

    Since [rewrite_loops] (which runs immediately before this pass -- see
    [rewrites_phase_1]) has already turned every loop into a self-recursive tail proc
    and transferred its [loop_contract_ext] onto that proc's [call_decl_contract_ext],
    loop termination checking falls out of this same pass with no separate code path. *)
let rec rewrite_contract_ext_calls (sm : scc_map) (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Call call_desc) ->
    let loc = Stmt.to_loc stmt in
    let* callee_qual_ident = Rewriter.resolve call_desc.call_name in
    let* callee_callable = Rewriter.find_and_reify_callable callee_qual_ident in
    let callee_call_decl = callee_callable.call_decl in
    if List.is_empty callee_call_decl.call_decl_contract_ext then
      Rewriter.return stmt
    else
      let* caller_qual_ident = Rewriter.current_scope_id in
      let* caller_callable = Rewriter.find_and_reify_callable caller_qual_ident in
      let* ext_hooks = Rewriter.current_ext_hooks in
      let same_scc_here = same_scc sm caller_qual_ident callee_qual_ident in
      let+ extra_stmts =
        ext_hooks.rewrite_contract_ext_call caller_callable.call_decl callee_call_decl
          same_scc_here call_desc.call_args loc
      in
      (match extra_stmts with
       | [] -> stmt
       | _ -> Stmt.mk_block_stmt ~loc (extra_stmts @ [ stmt ]))
  | _ -> Rewriter.Stmt.descend stmt ~f:(rewrite_contract_ext_calls sm)

let rec rewrite_new_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (New new_desc) ->
      let* () = Rewriter.Logs.debug (fun printers m ->
          m "Rewrites.rewrite_new_stmts: new_desc: %a" printers.pr_stmt stmt) in


      let assume_non_null_stmt = Stmt.mk_assume_expr ~loc:stmt.stmt_loc 
          ~cmnt:"AssumeNonNull Stmt; from new stmt"
        (Expr.mk_not (
          Expr.mk_eq (Expr.mk_null ())
          (Expr.mk_var ~typ:(Type.ref) new_desc.new_lhs)
        ))
      in
      let* validity_check_optns = 
        Rewriter.List.map new_desc.new_args ~f:(fun (fld_qi, e_opt) ->
          match e_opt with
          | None -> Rewriter.return None
          | Some e -> 
            let+ field_symbol = Rewriter.find_and_reify_field fld_qi in

            let field_ra_valid_qi =
              let field_ra = ProgUtils.field_get_ra_qual_iden field_symbol in
              ProgUtils.get_ra_valid_fn_qual_ident field_ra
            in
            let assert_stmt = 
              let error =
                ( Error.Verification,
                  stmt.stmt_loc,
                  "Could not prove validity of initially-allocated value" )
              in
              Stmt.mk_assert_expr ~loc:stmt.stmt_loc 
              ~cmnt:("new() stmt: " ^ Stmt.to_string stmt)
              ~spec_error:[ Stmt.mk_const_spec_error error ]
              (Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.bool
                (Expr.Var field_ra_valid_qi) [e]
              )
            in
            Some assert_stmt
          )
      in
      let validity_check_stmts = List.filter_map validity_check_optns ~f:(fun f -> f) in
      let havoc_stmt = Stmt.mk_havoc ~loc:stmt.stmt_loc
        (* ~cmnt:"RefVar Havoc Stmt; from new stmt" *)
        new_desc.new_lhs
      in

      let* new_inhale_stmts =
        Rewriter.List.map new_desc.new_args ~f:(fun (field_name, expr_optn) ->
            let* field_val =
              match expr_optn with
              | Some expr -> Rewriter.return expr
              | None ->
                  ProgUtils.get_field_utils_id field_name
            in

            let* field_type =
              let* field_symbol =
                Rewriter.find_and_reify field_name
              in
              match field_symbol with
              | FieldDef f -> Rewriter.return f.field_type
              | _ -> Error.internal_error stmt.stmt_loc "expected a field_def"
            in

            let inhale_expr =
              Expr.mk_app ~typ:Type.perm ~loc:stmt.stmt_loc Expr.Own
                [
                  Expr.mk_var ~typ:Type.ref new_desc.new_lhs;
                  Expr.mk_var ~typ:field_type field_name;
                  field_val;
                ]
            in

            let inhale_stmt =
              Stmt.mk_inhale_expr
                ~cmnt:("new stmt: " ^ Stmt.to_string stmt)
                ~loc:stmt.stmt_loc inhale_expr
            in

            Rewriter.return inhale_stmt)
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc:stmt.stmt_loc (
        validity_check_stmts @ 
        havoc_stmt :: 
        assume_non_null_stmt :: new_inhale_stmts))
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_new_stmts

(** Replaces a `fold p(x, y)` stmt with `exhale p(); inhale p.body`. *)
let rec rewrite_fold_unfold_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  let loc = stmt.stmt_loc in

  match stmt.stmt_desc with
  | Basic (Use use_desc) ->
      let* pred_qual_ident = Rewriter.resolve use_desc.use_name in
      let* symbol = Rewriter.find_and_reify use_desc.use_name in

      let pred_decl, body =
        match symbol with
        | CallDef c ->
            let spec =
              match c.call_def with
              | ProcDef p ->
                  Error.internal_error stmt.stmt_loc
                    "expected a func_def inside a fold/unfold stmt"
              | FuncDef { func_body = None } ->
                  Error.error stmt.stmt_loc (*(QualIdent.to_loc use_desc.use_name)*)
                    ("Cannot (un)fold abstract predicate " ^ (use_desc.use_name |> QualIdent.unqualify |> Ident.to_string)) (* TW: this should already be checked during typing *)
              | FuncDef { func_body = Some e } -> e
            in

            (c.call_decl, Expr.set_loc spec (Stmt.to_loc stmt))
        | _ -> Error.internal_error stmt.stmt_loc "expected a call_def"
      in

      begin match pred_decl.call_decl_kind, pred_decl.call_decl_is_auto with
      | Pred, true -> 
        let error =
          ( Error.Generic,
            loc,
            "Cannot (un)fold auto predicate: "
            ^ Ident.to_string pred_decl.call_decl_name )
        in
        Logs.warn (fun m -> m "%s" (Error.to_string error));
        Rewriter.return (Stmt.mk_skip ~loc)
      | _ -> 
      
      let truncated_formal_args, dropped_formal_args =
        List.split_n (pred_decl.call_decl_formals @ pred_decl.call_decl_returns)
          (List.length use_desc.use_args)
      in
      
      let new_dropped_args =
        List.map dropped_formal_args ~f:(fun var_decl ->
            {
              var_decl with
              var_name =
                Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
              var_loc = stmt.stmt_loc;
            })
      in
      
      let new_dropped_args_exprs =
        List.map new_dropped_args ~f:Expr.from_var_decl
      in
      let* _ =
        Rewriter.List.map new_dropped_args ~f:(fun var ->
            Rewriter.introduce_symbol
              (Module.VarDef { var_decl = var; var_init = None; var_is_free = NotFree }))
      in
      
      let new_renaming_map =
        List.fold2_exn
          (truncated_formal_args @ dropped_formal_args)
          (use_desc.use_args @ new_dropped_args_exprs)
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map var_decl arg_expr ->
              Map.add_exn map
                ~key:(QualIdent.from_ident var_decl.var_name)
                ~data:arg_expr)
      in
      
      let new_body =
        (Expr.alpha_renaming body new_renaming_map) |> (Fn.flip Expr.set_loc loc)
      in
        
      let existential_var_idens_set = Expr.existential_vars new_body in
      
      let user_exist_binds, user_exist_witnesses =
        match use_desc.use_kind with
        | Fold -> [], use_desc.use_witnesses_or_binds
        | Unfold -> use_desc.use_witnesses_or_binds, []
      in
      
      let* user_exist_binds_renam_map = 
        Rewriter.List.fold_left 
          user_exist_binds
        ~init:(Map.empty (module QualIdent)) ~f:(
          fun mp (bd_iden, exis_expr) ->
            let exis_iden = Expr.to_qual_ident exis_expr |> QualIdent.unqualify in
            match (Set.find existential_var_idens_set ~f:(
                fun ex_var_iden ->
                  String.(ex_var_iden.ident_name = exis_iden.ident_name)
              )) with
            | None -> Rewriter.return mp
            | Some v -> 
              
            Logs.debug (fun m -> m
              "Rewrites.rewrite_fold_unfold_stmts : 
                bd_iden = %a
                exis_iden = %a
              "
                Ident.pr bd_iden
                Ident.pr exis_iden
            );

            let+ bd_var_decl =
              
              let+ bd_var_symbol = Rewriter.find_and_reify (QualIdent.from_ident bd_iden) in

              begin match bd_var_symbol with
              | VarDef v -> v.var_decl
              | _ -> Error.internal_error stmt.stmt_loc "expected a var_def"
              end
            in


            let bd_var_expr = Expr.from_var_decl bd_var_decl in
            Map.set mp ~key:(QualIdent.from_ident v) ~data:bd_var_expr
        )
      in

      let user_witness_renam_map = 
        List.fold 
          user_exist_witnesses
        ~init:(Map.empty (module QualIdent)) ~f:(
          fun mp (iden, wtns_expr) ->
            
          match (Set.find existential_var_idens_set ~f:(
            fun ex_var_iden ->
              String.(ex_var_iden.ident_name = iden.ident_name)
          )) with
          | None -> mp
          | Some v -> Map.set mp ~key:(QualIdent.from_ident v) ~data:wtns_expr
        )
      in

      let body_fold_expr, body_unfold_expr =
        let exhale_expr = Expr.supply_witnesses user_witness_renam_map new_body in
        let inhale_expr = Expr.supply_witnesses user_exist_binds_renam_map new_body in

        exhale_expr, inhale_expr
      in

      let pred_expr =
          Expr.alpha_renaming 
            (Expr.mk_app ~loc ~typ:Type.bool
              (Expr.Var use_desc.use_name) (use_desc.use_args @ new_dropped_args_exprs))
            new_renaming_map
      in

      let new_stmt =
        match use_desc.use_kind with
        | Fold ->
          let spec_error =
            let error =
              ( Error.Verification,
                stmt.stmt_loc,
                "Failed to fold predicate. The body of the predicate may \
                 not hold at this point" )
            in
            [ Stmt.mk_const_spec_error error ]
          in
          let spec_form = Stmt.mk_spec ~spec_error body_fold_expr in
          let bind_stmt =
            Stmt.mk_bind ~loc:stmt.stmt_loc
              (List.map new_dropped_args ~f:(fun var_decl -> QualIdent.from_ident var_decl.var_name))
              spec_form
          in

          let inhale_stmt = 
            Stmt.mk_inhale_expr ~loc
              ~cmnt:("fold : " ^ Expr.to_string pred_expr)
              pred_expr 
          in
          
          let exhale_stmt =
            Stmt.mk_exhale_expr ~loc
              ~cmnt:("fold : " ^ Expr.to_string pred_expr)
              ~spec_error
              ~spec_source:(pred_qual_ident, 0)
              body_fold_expr
          in
          (match new_dropped_args with
          | [] -> Stmt.mk_block_stmt ~loc [ exhale_stmt; inhale_stmt ]
          | _ -> Stmt.mk_block_stmt ~loc [ bind_stmt; exhale_stmt; inhale_stmt ])

        | Unfold ->
          let inhale_stmt = 
            let usr_binds_havocs = 
              List.map use_desc.use_witnesses_or_binds ~f:(
                fun (i, e) -> 
                  Stmt.mk_havoc ~loc (QualIdent.from_ident i)
              )
            in
            
            let pred_body_inhale_stmt =
              Stmt.mk_inhale_expr ~loc
                ~cmnt:("unfold : " ^ Expr.to_string pred_expr)
                ~spec_source:(pred_qual_ident, 0)
                body_unfold_expr
            in
            
            Stmt.mk_block_stmt ~loc (usr_binds_havocs @ [pred_body_inhale_stmt])
          in

          let spec_error =
            let error =
              ( Error.Verification,
                stmt.stmt_loc,
                "Failed to unfold predicate. The predicate may not hold at \
                 this point" )
            in
            [ Stmt.mk_const_spec_error error ]
          in
          
          let bind_stmt =
            Stmt.mk_bind ~loc:stmt.stmt_loc
              (List.map new_dropped_args ~f:(fun var_decl -> QualIdent.from_ident var_decl.var_name))
              (Stmt.mk_spec pred_expr ~spec_error)
          in
          
          let exhale_stmt =
            
            Stmt.mk_exhale_expr ~loc
                ~cmnt:("unfold : " ^ Expr.to_string pred_expr)
                ~spec_error
                pred_expr
          in
          match new_dropped_args with
          | [] -> Stmt.mk_block_stmt ~loc [ exhale_stmt; inhale_stmt ]
          | _ -> Stmt.mk_block_stmt ~loc [ bind_stmt; exhale_stmt; inhale_stmt ]
      in
      Rewriter.return new_stmt
      end
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_fold_unfold_stmts

let rec rewrite_call_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Call call_desc) -> (
      let* callee_qual_ident = Rewriter.resolve call_desc.call_name in
      let* symbol = Rewriter.find_and_reify call_desc.call_name in

      let call_decl, call_def =
        match symbol with
        | CallDef c ->
          if call_desc.call_is_spawn
          then ({c.call_decl with call_decl_postcond = []; call_decl_returns= []}, c.call_def)
          else (c.call_decl, c.call_def)
        | _ -> Error.internal_error stmt.stmt_loc "expected a call_def"
      in

      let _, dropped_returns =
        List.split_n call_decl.call_decl_returns
          (List.length call_desc.call_lhs)
      in

      let* fresh_dropped_returns =
        Rewriter.List.map dropped_returns ~f:(fun var_decl ->
            let new_var_decl = {
              var_decl with
              var_name =
                Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
              var_loc = stmt.stmt_loc;
            }
            in
            let+ _ =
              Rewriter.introduce_symbol
                (Module.VarDef { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
            in
            new_var_decl)
      in
        
     let* lhs_list =
        Rewriter.List.map call_desc.call_lhs ~f:(fun qual_iden ->
            let* symbol = Rewriter.find_and_reify qual_iden in

            match symbol with
            | VarDef v -> Rewriter.return v.var_decl
            | _ ->
                Error.internal_error stmt.stmt_loc
                  ("expected a variable; found " ^ Symbol.to_string symbol))
      in
      let lhs_list = lhs_list @ fresh_dropped_returns in

      let* new_lhs_list =
        Rewriter.List.map lhs_list ~f:(fun lhs ->
            let new_var_name =
              Ident.fresh stmt.stmt_loc (lhs.var_name.ident_name ^ "$ret")
            in
            let new_var_decl = { lhs with var_name = new_var_name } in
            let* _ =
              Rewriter.introduce_symbol
                (Module.VarDef { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
            in

            Rewriter.return (Expr.from_var_decl new_var_decl))
      in

      let* new_renaming_map,
           new_dropped_args =
        let truncated_formal_args, dropped_formal_args =
          List.split_n call_decl.call_decl_formals
            (List.length call_desc.call_args)
        in

        let fresh_dropped_args =
          List.map dropped_formal_args ~f:(fun var_decl ->
              {
                var_decl with
                var_name =
                  Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
                var_loc = stmt.stmt_loc;
              })
        in

        let fresh_dropped_args_exprs =
          List.map fresh_dropped_args ~f:Expr.from_var_decl
        in

        (* Need to ensure that call_decl_returns and call_desc.call_lhs line up *)
        let renaming_map =
          List.fold2_exn
            (truncated_formal_args @ dropped_formal_args
           @ call_decl.call_decl_returns)
            (call_desc.call_args @ fresh_dropped_args_exprs @ new_lhs_list)
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl arg_expr ->
              Map.add_exn map
                ~key:(QualIdent.from_ident var_decl.var_name)
                ~data:arg_expr)
        in

        Rewriter.return
          (renaming_map, fresh_dropped_args)
      in

      let* () = Rewriter.Logs.debug (fun printers m ->
          m "Rewrites.rewrite_call_stmts: new_renaming_map: %a"
            (Util.Print.pr_map ~key:QualIdent.pr ~value:printers.pr_expr)
            new_renaming_map) in

      match call_def with
      | ProcDef _ ->
          let* _ =
            Rewriter.List.map new_dropped_args ~f:(fun var ->
                Rewriter.introduce_symbol
                  (Module.VarDef { var_decl = var; var_init = None; var_is_free = NotFree }))
          in

          (* let build_exhale_spec (spec: Stmt.spec) =
               (* renames args from old to new. Also, existentially quantifies over relevant implicit variables. *)
               let spec_form = Expr.alpha_renaming spec.spec_form renaming_map in

               let used_implicit_vars = List.filter (List.zip_exn quant_dropped_args new_dropped_args) ~f:(
                 fun (var_decl1, var_decl2) ->
                   Set.mem (Expr.local_vars spec_form) var_decl1.var_name
               ) in

               let eqs = List.map used_implicit_vars ~f:(fun (v_d1, v_d2) -> Expr.mk_eq (Expr.from_var_decl v_d1) (Expr.from_var_decl v_d2)) in

               let used_quant_vars, _ = List.unzip used_implicit_vars in

               let spec_form = Expr.mk_binder ~loc:stmt.stmt_loc ~typ:Type.bool Exists used_quant_vars (Expr.mk_and (spec_form :: eqs)) in

               { spec with spec_form }
             in

             let build_inhale_spec (spec: Stmt.spec) =
               let spec_form = Expr.alpha_renaming spec.spec_form renaming_map2 in

               { spec with spec_form }
             in *)
          let spec_error =
            match (List.map call_decl.call_decl_precond ~f:(fun spec -> spec.spec_error)) with
            | (_ :: _ as err) :: _ -> err
            | _ -> []
          in
          let spec_form =
            Stmt.mk_spec
              ~cmnt:("Bind stmt for Call: " ^ Stmt.to_string stmt)
              ~spec_error 
              (Expr.mk_and
                 (List.map call_decl.call_decl_precond ~f:(fun spec ->
                      Expr.alpha_renaming spec.spec_form new_renaming_map)))
          in
          
          let bind_stmt =
            (* TODO: can we preserve the error messages for the individual preconditions here? *)
            Stmt.mk_bind ~loc:stmt.stmt_loc
               (List.map new_dropped_args ~f:(fun var_decl -> QualIdent.from_ident var_decl.var_name))
               spec_form
          in

          let exhale_stmts =
            List.mapi call_decl.call_decl_precond ~f:(fun i spec ->
                (* Logs.debug (fun m -> m "Rewrites.rewrite_call_stmts: Exhale_stmt=%a; Exhale_stmt_error_len = %i; Exhale_stmt_error=%s" Expr.pr spec.spec_form (List.length spec_error) (Error.to_string ((List.hd_exn spec_error) (QualIdent.from_ident call_decl.call_decl_name) stmt.stmt_loc)) ); *)

                Stmt.mk_exhale_expr ~loc:stmt.stmt_loc
                  ~cmnt:("Exhale stmt for Call: " ^ Stmt.to_string stmt)
                  ~spec_error:spec.spec_error
                  ~spec_source:(callee_qual_ident, i)
                  (Expr.alpha_renaming spec.spec_form new_renaming_map))
          in

          (* One inhale per postcond clause (rather than a single inhale of their
             conjunction) so each can carry its own [spec_source] -- `assume (p && q)`
             and `assume p; assume q` are equivalent, so this is not an observable
             behavior change. *)
          let num_precond = List.length call_decl.call_decl_precond in
          let inhale_stmts =
            List.mapi call_decl.call_decl_postcond ~f:(fun j spec ->
                Stmt.mk_inhale_expr ~loc:stmt.stmt_loc
                  ~cmnt:("Inhale stmt for Call: " ^ Stmt.to_string stmt)
                  ~spec_source:(callee_qual_ident, num_precond + j)
                  (Expr.alpha_renaming spec.spec_form new_renaming_map))
          in

          let reassign_lhs_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc ~is_init:call_desc.call_is_init
              (List.map lhs_list ~f:(fun decl -> QualIdent.from_ident decl.var_name))
              (Expr.mk_tuple new_lhs_list)
          in

          (* TODO: Need to havoc ret vars before inhaling postconditions *)
          let new_stmt =
            Stmt.mk_block_stmt ~loc:stmt.stmt_loc
              (* (if (List.is_empty call_decl.call_decl_precond ) then *)
              (* [inhale_stmt] *)
              (* else *)
              (match (new_dropped_args, lhs_list) with
              | [], [] -> exhale_stmts @ inhale_stmts
              | [], _ -> exhale_stmts @ inhale_stmts @ [ reassign_lhs_stmt ]
              | _, [] ->
                  (bind_stmt :: exhale_stmts) @ inhale_stmts
              | _, _ ->
                  (bind_stmt :: exhale_stmts)
                  @ inhale_stmts @ [ reassign_lhs_stmt ])
          in

          Rewriter.return new_stmt
      | FuncDef _ ->
          (* No exhale here: func/pred/invariant contracts can't carry a `requires`
             (see [Typing.check_no_requires_on_pure_callables]), so there is nothing to
             check at this call site. *)
          let ret_typ =
            Type.mk_prod stmt.stmt_loc
              (List.map call_decl.call_decl_returns ~f:(fun var_decl ->
                   var_decl.var_type))
          in

          let new_assign_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc (List.map new_lhs_list ~f:Expr.to_qual_ident)
              (Expr.mk_app ~loc:stmt.stmt_loc ~typ:ret_typ
                 (Expr.Var call_desc.call_name) call_desc.call_args)
          in

          let reassign_lhs_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc
              (List.map lhs_list ~f:(fun decl -> QualIdent.from_ident decl.var_name))
              (Expr.mk_tuple new_lhs_list)
          in

          let new_stmt =
            Stmt.mk_block_stmt ~loc:stmt.stmt_loc
              (match lhs_list with
              | [] -> [ new_assign_stmt ]
              | _ -> [ new_assign_stmt; reassign_lhs_stmt ])
          in

          Rewriter.return new_stmt)
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_call_stmts

let rewrite_callable_pre_post_conds (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_def with
  | ProcDef proc -> (
      match proc.proc_body with
      | None -> Rewriter.return c
      | Some body ->
          let loc = Stmt.to_loc body in
          let* own_qual_ident = Rewriter.current_scope_id in
          let num_precond = List.length c.call_decl.call_decl_precond in
          let pre_conds =
            List.filter_mapi c.call_decl.call_decl_precond ~f:(fun i spec ->
                if spec.spec_atomic then None
                else
                  let spec = { spec with spec_source = Some (own_qual_ident, i) } in
                  Some
                    (Stmt.mk_inhale_spec
                       ~cmnt:("precond: " ^ Expr.to_string spec.spec_form)
                       ~loc:(Expr.to_loc spec.spec_form)
                       spec))
          and post_conds =
            List.filter_mapi c.call_decl.call_decl_postcond ~f:(fun j spec ->
                if spec.spec_atomic then None
                else
                  let spec =
                    { spec with spec_source = Some (own_qual_ident, num_precond + j) }
                  in
                  Some
                    (Stmt.mk_exhale_spec
                       ~cmnt:("postcond: " ^ Expr.to_string spec.spec_form)
                       ~loc:(Stmt.to_loc body |> Loc.to_end)
                       spec))
          in

          let* pre_conds, post_conds =
            if not (Callable.is_atomic c.call_decl) then
              Rewriter.return (pre_conds, post_conds)
            else
              let* callable_fully_qual_name = Rewriter.current_scope_id in

              let atomic_token_var =
                Expr.mk_var ~typ:(Type.atomic_token callable_fully_qual_name)
                  (QualIdent.from_ident
                     (ProgUtils.callable_au_token_ident ~loc
                        c.call_decl.call_decl_name))
              in

              let concrete_args =
                List.filter c.call_decl.call_decl_formals ~f:(fun var_decl ->
                    not var_decl.var_implicit)
              in
              let concrete_args_expr =
                List.map concrete_args ~f:Expr.from_var_decl
              in

              let inhale_au =
                Stmt.mk_inhale_expr ~cmnt:("au_precond") ~loc
                  (Expr.mk_app ~loc ~typ:Type.perm
                     (Expr.AUPred callable_fully_qual_name)
                     [atomic_token_var; Expr.mk_tuple concrete_args_expr])
              in

              let exhale_au =
                let ret_vars =
                  List.map c.call_decl.call_decl_returns ~f:(fun var_decl ->
                      Expr.from_var_decl var_decl)
                in
                let ret_expr = Expr.mk_tuple ~loc ret_vars in
                let error =
                  ( Error.Verification,
                    loc |> Loc.to_end,
                    "The atomic specification may not have been committed \
                     before reaching this return point" )
                in
                Stmt.mk_exhale_expr ~cmnt:("au_postcond") ~loc
                  ~spec_error:[ Stmt.mk_const_spec_error error ]
                  (Expr.mk_app ~loc ~typ:Type.perm
                     (Expr.AUPredCommit callable_fully_qual_name)
                     [atomic_token_var; Expr.mk_tuple concrete_args_expr; ret_expr ])
              in

              Rewriter.return (inhale_au :: pre_conds, exhale_au :: post_conds)
          in

          let new_body =
            Stmt.mk_block_stmt ~loc (pre_conds @ [ body ] @ post_conds)
          in
          let new_proc =
            Callable.
              {
                call_decl = c.call_decl;
                call_def = ProcDef { proc_body = Some new_body };
              }
          in
          Rewriter.return new_proc)
  | FuncDef func -> Rewriter.return c

let rec rewrite_add_pred_implicit_args (expr : Expr.t) : Expr.t Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | App (Var qual_iden, args, expr_attr) ->
    let* symbol = Rewriter.find_and_reify qual_iden in
    begin match symbol with
    | CallDef callable when 
        Poly.(callable.call_decl.call_decl_kind = Callable.Pred ||
        callable.call_decl.call_decl_kind = Callable.Invariant) ->
      let* callable = Rewriter.find_and_reify_callable qual_iden in
        let* () = Rewriter.Logs.debug (fun printers m -> m "Rewrites.rewrite_add_pred_implicit_args called on: %a; callable = %a" printers.pr_expr expr printers.pr_callable callable) in
        if List.length (callable.call_decl.call_decl_formals @ callable.call_decl.call_decl_returns) = List.length args then
          Rewriter.return expr
        else 
          (
          let dropped_args = List.drop (callable.call_decl.call_decl_formals @ callable.call_decl.call_decl_returns) (List.length args) in
          let new_dropped_args = List.map dropped_args ~f:(fun var_decl ->
            {
              var_decl with
              var_name =
                Ident.fresh expr_attr.expr_loc var_decl.var_name.ident_name;
                var_loc = expr_attr.expr_loc
            })
          in
          Rewriter.return (Expr.mk_binder ~loc:expr_attr.expr_loc ~typ:Type.perm Exists new_dropped_args 
          (App (Var qual_iden, args @ (List.map new_dropped_args ~f:(Expr.from_var_decl)), expr_attr))))
    | _ -> Rewriter.return expr
    end
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_add_pred_implicit_args
  
let rewrite_atomic_callable_token (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_def with
  | ProcDef proc -> (
      match proc.proc_body with
      | None -> Rewriter.return c
      | Some body ->
          let loc = Stmt.to_loc body in
          let* curr_proc_name = Rewriter.current_scope_id in
          if not (Callable.is_atomic c.call_decl) then Rewriter.return c
          else
            let atomic_token_var =
              {
                Type.var_name =
                  ProgUtils.callable_au_token_ident ~loc
                    c.call_decl.call_decl_name;
                var_loc = loc;
                var_type = Type.atomic_token curr_proc_name;
                var_const = false;
                var_ghost = true;
                var_implicit = false;
              }
            in

            let* _ =
              Rewriter.introduce_symbol
                (Module.VarDef { var_decl = atomic_token_var; var_init = None; var_is_free = NotFree })
            in

            Rewriter.return c)
  | FuncDef func -> Rewriter.return c

let rec rewrite_frac_field_types (symbol : Module.symbol) :
    Module.symbol Rewriter.t =
  let open Rewriter.Syntax in
  match symbol with
  | ModDef _ | ModInst _ | TypeDef _ | ConstrDef _ | DestrDef _ | VarDef _
  | CallDef _ ->
      Rewriter.return symbol
  (* A manifest field shares the target's resource algebra: it takes the
     target's type as already rewritten rather than being wrapped in a Frac of
     its own, which would be a distinct RA over one heap. The field's type feeds
     the Frac module's name (see [rewrite_own_expr_4_arg]), so leaving it as the
     pre-rewrite type derives the wrong name. *)
  | FieldDef ({ field_alias = Some target; _ } as f) ->
      let* target_field = Rewriter.find_and_reify_field target in
      (* The alias generates no Frac module of its own, but a name derived from it can
         still be asked for: a callee whose contract was rewritten before this module
         existed carries `<A>.Frac$f` with `A` substituted to the alias's module, and
         nothing re-derives it from the resolved field at that point. Register the name
         as another spelling of the target's, the same way the field itself is
         registered as another spelling of the target. *)
      let* () =
        let* is_field_an_ra =
          ProgUtils.is_ra_type (Type.field_val target_field.field_type)
        in
        if is_field_an_ra then Rewriter.return ()
        else
          let* target = Rewriter.resolve target in
          Rewriter.add_transparent
            (ProgUtils.frac_field_to_frac_mod_ident ~loc:f.field_loc f.field_name
               target_field.field_type)
            (ProgUtils.frac_field_to_frac_mod_qual_ident ~loc:f.field_loc target
               target_field.field_type)
      in
      Rewriter.return (Module.FieldDef { f with field_type = target_field.field_type })
  | FieldDef f ->
      let* is_field_an_ra = ProgUtils.is_ra_type (Type.field_val f.field_type) in

      let* () = Rewriter.Logs.debug (fun printers m -> m
          "Rewrites.rewrite_frac_field_types:
          is_field_an_ra: %a -> %b"
            printers.pr_type f.field_type
            is_field_an_ra
      ) in
            
      if is_field_an_ra then Rewriter.return symbol
      else
        let* field_type =
          Typing.ProcessTypeExpr.expand_type_expr f.field_type
        in
        let field_underlying_tp =
          match field_type with
          | App (Fld, [ tp_expr ], _) -> tp_expr
          | _ -> Error.type_error f.field_loc "Expected field identifier."
        in

        let* tp_module =
          ProgUtils.intros_type_module ~loc:f.field_loc
            ~f:Typing.process_symbol field_underlying_tp
        in

        let instantiated_frac_module =
          Module.ModInst
            {
              mod_inst_name =
                ProgUtils.frac_field_to_frac_mod_ident ~loc:f.field_loc 
                  f.field_name field_type;
              mod_inst_type = Predefs.lib_cancellative_ra_mod_qual_ident;
              mod_inst_def =
                Some (Predefs.lib_frac_mod_qual_ident, [ Module.ModArg tp_module ]);
              mod_inst_is_interface = false;
              mod_inst_is_free = false;
              mod_inst_loc = f.field_loc;
            }
        in

        (* let* topscope_name = ProgUtils.find_highest_valid_scope_type_expr f.field_loc field_underlying_tp in

           let topscope_name = match topscope_name with
             | Some topscope_name -> topscope_name
             | None -> Error.type_error f.field_loc ("Could not find a valid scope to add field " ^ (Ident.to_string f.field_name) ^ " to.")

           in *)
        let* frac_mod_name =
          Rewriter.introduce_typecheck_symbol ~loc:f.field_loc
            ~f:Typing.process_symbol instantiated_frac_module
        in

        Logs.debug (fun m -> m 
          "Rewrites.rewrite_frac_field_types: 
          frac_mod_name: %a"

            QualIdent.pr frac_mod_name
        );

        let frac_type =
          Type.mk_fld f.field_loc
            (Type.mk_var
               (QualIdent.append frac_mod_name (Ident.make f.field_loc "T" 0)))
        in

        Rewriter.return (Module.FieldDef { f with field_type = frac_type })

(** Settle how each symbol an expression names is spelled, now that the resource
    algebras and heap utilities a field needs have been generated.

    Those artifacts are generated per field and named after it, so they exist only under
    the name of the field they belong to. A manifest field has none of its own -- it
    shares the ones belonging to the field it stands for -- and reaches them through
    aliases registered beside it. That is enough for the front end, which resolves; it is
    not enough for the backend, which keys on the name it is handed. A contract reaching
    a call site through a functor instantiated at a module with a manifest field is
    exactly that case: reifying the callee substitutes its formal for the argument module
    syntactically, so the contract comes out naming `Adapt.Frac$f` for a resource algebra
    that only ever existed as `Client.Frac$bit`.

    Only qualified names are touched -- an unqualified one is a formal or a local, which
    resolution has no business rewriting -- and anything that does not resolve is left
    exactly as it was. Types are left alone: they are canonical already, having been
    expanded on the way here. *)
let canonicalize_symbols (expr : Expr.t) : Expr.t Rewriter.t =
  let open Rewriter.Syntax in
  let canonicalize qual_ident =
    if List.is_empty (QualIdent.path qual_ident) then Rewriter.return qual_ident
    else
      let+ resolved = Rewriter.resolve_opt qual_ident in
      Option.value resolved ~default:qual_ident
  in
  Rewriter.Expr.rewrite_qual_idents_m ~f:canonicalize expr

let rec rewrite_own_expr_4_arg (expr : Expr.t) : Expr.t Rewriter.t =
  (* Rewrites expressions of the form `own(x, f, v, p)` to `own (x, f, Frac[f.type].frac_chunk(v, p))

     Essentially, makes a uniform 3-arg representation of all own expressions, frac-type as well as RA type.
  *)
  let open Rewriter.Syntax in
  let* () = Rewriter.Logs.debug (fun printers m ->
      m "Rewrites.rewrite_own_expr_4_arg: run on expr: %a" printers.pr_expr expr) in

  match expr with
  | App (Own, [ expr1; expr2; expr3; expr4 ], expr_attr) ->
      let* () = Rewriter.Logs.debug (fun printers m ->
          m "Rewrites.rewrite_own_expr_4_arg: found expr: %a" printers.pr_expr expr) in

      (* let field_type = match Expr.to_type expr2 with
           | App (Fld, [tp_expr], _) -> tp_expr
           | _ -> Error.type_error (Expr.to_loc expr2) "Expected field identifier."
         in *)
      let field_type = Expr.to_type expr2 in

      let* () = Rewriter.Logs.debug (fun printers m -> m
        "Rewrites.rewrite_own_expr_4_arg: field_type1: %a"
          printers.pr_type field_type
      ) in

      let* field_type = Typing.ProcessTypeExpr.expand_type_expr field_type in
      let field_name = QualIdent.unqualify (Expr.to_qual_ident expr2) in

      let* () = Rewriter.Logs.debug (fun printers m -> m
        "Rewrites.rewrite_own_expr_4_arg: field_type2: %a"
          printers.pr_type field_type
      ) in

      let+ expr3 =
        let expr3_1 = expr3 in
        let expr3_2 = expr4 in

        let* () = Rewriter.Logs.debug (fun printers m ->
            m
              "Rewrites.rewrite_own_expr_4_arg: intros_type_module started: \
               tp_module: %a;\n ... & frac_mod_ident: %a"
              printers.pr_type field_type QualIdent.pr (QualIdent.from_ident
              (ProgUtils.frac_field_to_frac_mod_ident
                 ~loc:(Expr.to_loc expr) field_name field_type))) in

        let* frac_mod_name =
          (* Resolve the field before deriving its Frac module's name. A callee's
             contract reaches here with the instantiation substitution already
             applied syntactically (`H.f` -> `Adapt.f`), so the name was never put
             through the symbol table; without this a manifest field would look
             for an RA module beside the alias rather than beside the field it
             stands for. *)
          let* field_qual_ident = Rewriter.resolve (Expr.to_qual_ident expr2) in
          let frac_mod_name =
            ProgUtils.frac_field_to_frac_mod_qual_ident ~loc:(Expr.to_loc expr) field_qual_ident field_type
          in

          Logs.debug (fun m -> m
            "Rewrites.rewrite_own_expr_4_args: \ 
            frac_mod_name: %a"

              QualIdent.pr frac_mod_name 
          );

          Rewriter.resolve frac_mod_name
          
        in

        let frac_type =
          Type.mk_var
            (QualIdent.append frac_mod_name
               (Ident.make (Expr.to_loc expr) "T" 0))
        in
        (* let frac_constr = Rewriter.find_and_reify (Expr.to_loc expr) (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "frac_chunk" 0)) in *)
        let expr3 =
          Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:frac_type
            (Expr.DataConstr
               (QualIdent.append frac_mod_name
                  (Ident.make (Expr.to_loc expr) "frac_chunk" 0)))
            [ expr3_1; expr3_2 ]
        in

        let* () = Rewriter.Logs.debug (fun printers m -> m
          "Rewrites.rewrite_own_expr_4_arg:
            expr3: %a"

            printers.pr_expr expr3
        ) in

        Rewriter.return expr3
      in

      Expr.App (Own, [ expr1; expr2; expr3 ], expr_attr)
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_own_expr_4_arg

let rec rewrite_new_fpu_stmt_heap_arg (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  (* Logs.debug (fun m -> m "Rewrites.rewrite_new_fpu_stmt_heap_arg: stmt: %a" Stmt.pr stmt); *)
  match stmt.stmt_desc with
  | Basic (New new_desc) ->
      let* new_args =
        Rewriter.List.map new_desc.new_args ~f:(fun (field_name, expr_optn) ->
            match expr_optn with
            | None -> Rewriter.return (field_name, expr_optn)
            | Some expr ->
                let* expr_typ =
                  Typing.ProcessTypeExpr.expand_type_expr (Expr.to_type expr)
                in

                let* field_elem_type =
                  let+ field_symbol =
                    Rewriter.find_and_reify field_name
                  in

                  match field_symbol with
                  | FieldDef f -> (
                      match f.field_type with
                      | App (Fld, [ tp_expr ], _) -> tp_expr
                      | _ ->
                          Error.type_error (Expr.to_loc expr)
                            "Expected field identifier.")
                  | _ -> Error.internal_error stmt.stmt_loc "expected a field_def"
                in

                let* field_elem_typ_expanded =
                  Typing.ProcessTypeExpr.expand_type_expr field_elem_type
                in

                if Type.(expr_typ = field_elem_typ_expanded) then
                  Rewriter.return (field_name, expr_optn)
                else
                  let frac_mod_name =
                    match field_elem_type with
                    | App (Var qual_iden, _, _) -> QualIdent.pop qual_iden
                    | _ ->
                        Error.type_error (Expr.to_loc expr)
                          "Expected field identifier."
                  in

                  let frac_type =
                    Type.mk_var 
                      (QualIdent.append frac_mod_name
                         (Ident.make (Expr.to_loc expr) "T" 0))
                  in
                  let new_expr =
                    Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:frac_type
                      (Expr.DataConstr
                         (QualIdent.append frac_mod_name
                            (Ident.make (Expr.to_loc expr) "frac_chunk" 0)))
                      [ expr; Expr.mk_real 1.0 ]
                  in

                  Rewriter.return (field_name, Some new_expr))
      in

      Rewriter.return
        { stmt with stmt_desc = Basic (New { new_desc with new_args }) }
  | Basic (Fpu fpu_desc) ->
      let compute_new_expr old_expr field_name =
        let loc = Expr.to_loc old_expr in
        let* expr_typ =
          Typing.ProcessTypeExpr.expand_type_expr (Expr.to_type old_expr)
        in

        let* field_elem_type =
          let+ field_symbol = Rewriter.find_and_reify field_name in

          match field_symbol with
          | FieldDef f -> (
              match f.field_type with
              | App (Fld, [ tp_expr ], _) -> tp_expr
              | _ -> Error.type_error loc "Expected field identifier.")
          | _ -> Error.internal_error stmt.stmt_loc "expected a field_def"
        in

        let* field_elem_typ_expanded =
          Typing.ProcessTypeExpr.expand_type_expr field_elem_type
        in

        if Type.(expr_typ = field_elem_typ_expanded) then
          Rewriter.return old_expr
        else
          let* field_type =
            let+ field_symbol = Rewriter.find_and_reify field_name in

            match field_symbol with
            | FieldDef f -> f.field_type
            | _ -> Error.internal_error stmt.stmt_loc "expected a field_def"
          in

          let frac_mod_name =
            match field_elem_type with
            | App (Var qual_iden, _, _) -> QualIdent.pop qual_iden
            | _ -> Error.type_error loc "Expected field identifier."
          in

          let frac_type =
            Type.mk_var
              (QualIdent.append frac_mod_name (Ident.make loc "T" 0))
          in
          let new_expr =
            Expr.mk_app ~loc ~typ:frac_type
              (Expr.DataConstr
                 (QualIdent.append frac_mod_name
                    (Ident.make loc "frac_chunk" 0)))
              [ old_expr; Expr.mk_real 1.0 ]
          in

          Rewriter.return new_expr
      in

      let* fpu_old_val =
        match fpu_desc.fpu_old_val with
        | None -> Rewriter.return None
        | Some expr ->
            let+ new_expr = compute_new_expr expr fpu_desc.fpu_field in
            Some new_expr
      in

      let* fpu_new_val =
        compute_new_expr fpu_desc.fpu_new_val fpu_desc.fpu_field
      in

      let new_fpu_desc = { fpu_desc with fpu_old_val; fpu_new_val } in

      Rewriter.return { stmt with stmt_desc = Basic (Fpu new_fpu_desc) }
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_new_fpu_stmt_heap_arg

let rewrite_add_predicate_validity_lemmas (c : Callable.t) :
    Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  if is_free c.call_decl.call_decl_status then Rewriter.return c else
  match c.call_decl.call_decl_kind with
  | Pred | Invariant -> (
      match (c.call_decl.call_decl_returns, c.call_def) with
      | [], _ | _, FuncDef { func_body = None } -> Rewriter.return c
      | rets, FuncDef { func_body = Some body }  ->
          let pred_valid_lemma_ident =
            Ident.fresh c.call_decl.call_decl_loc
              ("pred_valid$" ^ Ident.to_string c.call_decl.call_decl_name)
          in

          let formal_args, renaming_map1, renaming_map2, postconds =
            let renamings, in_args =
              List.fold_map c.call_decl.call_decl_formals
                ~init:(Map.empty (module QualIdent))
                ~f:(fun acc_renamings var_decl ->
                  let new_var_decl =
                    {
                      var_decl with
                      var_name =
                        Ident.fresh var_decl.var_loc
                          var_decl.var_name.ident_name;
                    }
                  in
                  let new_var_expr = Expr.from_var_decl new_var_decl in

                  ( Map.add_exn acc_renamings
                      ~key:(QualIdent.from_ident var_decl.var_name)
                      ~data:new_var_expr,
                    new_var_decl ))
            in

            let renamings1, out_args1 =
              List.fold_map rets ~init:renamings
                ~f:(fun acc_renamings var_decl ->
                  let new_var_decl =
                    {
                      var_decl with
                      var_name =
                        Ident.fresh var_decl.var_loc
                          var_decl.var_name.ident_name;
                    }
                  in
                  let new_var_expr = Expr.from_var_decl new_var_decl in

                  ( Map.add_exn acc_renamings
                      ~key:(QualIdent.from_ident var_decl.var_name)
                      ~data:new_var_expr,
                    new_var_decl ))
            in

            let renamings2, out_args2 =
              List.fold_map rets ~init:renamings
                ~f:(fun acc_renamings var_decl ->
                  let new_var_decl =
                    {
                      var_decl with
                      var_name =
                        Ident.fresh var_decl.var_loc
                          var_decl.var_name.ident_name;
                    }
                  in
                  let new_var_expr = Expr.from_var_decl new_var_decl in

                  ( Map.add_exn acc_renamings
                      ~key:(QualIdent.from_ident var_decl.var_name)
                      ~data:new_var_expr,
                    new_var_decl ))
            in

            let postconds =
              List.map2_exn out_args1 out_args2 ~f:(fun out_arg1 out_arg2 ->
                  let spec_expr =
                    (Expr.mk_eq ~loc:(Expr.to_loc body)
                       (Expr.from_var_decl out_arg1)
                       (Expr.from_var_decl out_arg2))
                  in
                  let error =
                    (Error.Verification,
                     out_arg1.var_loc,
                     "This output parameter may not be uniquely determined by the input parameter(s)")
                  in
                  Stmt.mk_spec ~spec_error:[fun _ _ -> error] spec_expr)
            in

            (in_args @ out_args1 @ out_args2, renamings1, renamings2, postconds)
          in

          (*let postcond =
            let error = (Error.Verification, 
             (Expr.mk_bool ~loc:(Expr.to_loc body) false)
          in*)

          let call_decl =
            {
              Callable.call_decl_kind = Lemma;
              call_decl_name = pred_valid_lemma_ident;
              call_decl_formals = formal_args;
              call_decl_returns = [];
              call_decl_locals = [];
              call_decl_precond = [];
              call_decl_postcond = postconds;
              call_decl_contract_ext = [];
              call_decl_status = NotFree;
              call_decl_is_auto = false;
              (* This callable is created in `rewrites_phase_3`, after
                 `Masks.compute_masks`/atomicity analysis have already run, so
                 it never goes through the mask fixpoint and `call_decl_needs_mask`
                 would otherwise be stuck at `None` forever. Safe to seed it
                 as `Some []` directly: the body below is just two `inhale`s
                 -- structurally impossible to unfold an invariant, so it can
                 never have a real mask requirement. *)
              call_decl_needs_mask = Some [];
              call_decl_grants_mask = Some [];
              call_decl_loc = c.call_decl.call_decl_loc;
               call_decl_loc_params = [];
            }
          in

          let* pred_qual_ident = Rewriter.current_scope_id in

          let call_body =
            Stmt.mk_block_stmt ~loc:c.call_decl.call_decl_loc
              [
                Stmt.mk_inhale_expr ~loc:c.call_decl.call_decl_loc
                  ~spec_source:(pred_qual_ident, 0)
                  (Expr.alpha_renaming body renaming_map1);
                Stmt.mk_inhale_expr ~loc:c.call_decl.call_decl_loc
                  ~spec_source:(pred_qual_ident, 0)
                  (Expr.alpha_renaming body renaming_map2);
              ]
          in

          let call_def =
            Module.CallDef
              Callable.
                { call_decl; call_def = ProcDef { proc_body = Some call_body } }
          in

          let* _ =
            Rewriter.introduce_typecheck_symbol ~loc:c.call_decl.call_decl_loc
              ~f:Typing.process_symbol call_def
          in

          Rewriter.return c
      | _, ProcDef _ ->
          Error.internal_error c.call_decl.call_decl_loc
            "Expected a function definition for a predicate")
  | _ -> Rewriter.return c


(** For every [func] with a body and a non-empty [ensures] clause, synthesizes a companion
    "auto lemma" that proves the func satisfies its own postcondition, and whose body structurally
    mirrors the func's body expression: wherever the body branches on a condition (the [?:]
    ternary), the lemma's body has a matching if/else statement; and wherever the body calls
    another func that itself has such a companion lemma (including calling itself, or a
    mutually-recursive sibling func), the lemma's body invokes that other func's companion lemma
    at the same (guarded) position with the same arguments. Being an auto lemma, once its body is
    verified (which, since it is an ordinary recursive/mutually-recursive lemma call, is checked via
    the standard call-rule -- providing the induction hypothesis needed for the recursive case) its
    postcondition becomes globally available, which is exactly the fact the func's own (otherwise
    unprovable for recursive funcs) contract needs. The original func is left untouched; the
    verification of its contract in the back-end relies solely on this generated lemma (see
    [rewrite_callable_pre_post_conds] / [Callable.call_decl_status] handling for that func). *)
let rec rewrite_add_func_contract_lemmas (sm : scc_map) (m : Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in
  let* _ = Rewriter.enter_module m in

  let* mod_def =
    Rewriter.List.map m.mod_def ~f:(function
      | Module.SymbolDef (ModDef mod_def) ->
          let+ mod_def = rewrite_add_func_contract_lemmas sm mod_def in
          Module.SymbolDef (Module.ModDef mod_def)
      | instr -> Rewriter.return instr)
  in
  let m = { m with mod_def } in

  (* A func needs this pass's scaffolding either to prove its own postcondition (the
     pass's original purpose) or -- even with no postcondition at all -- to give a
     contract extension (e.g. `decreases`) a lemma body to instrument, since a func's
     own body is a pure expression with no call site of its own. Without the second
     disjunct, a func with e.g. a `decreases` clause but no `ensures` clause would
     never get a companion lemma, so its self-recursive calls would never be walked by
     [gen_stmts] below, silently skipping the contract-extension check entirely. *)
  let eligible =
    List.filter_map m.mod_def ~f:(function
      | Module.SymbolDef
          (CallDef
            ({ call_decl; call_def = FuncDef { func_body = Some body } } : Callable.t))
        when Poly.(call_decl.call_decl_kind = Func)
             && (not (List.is_empty call_decl.call_decl_postcond)
                 || not (List.is_empty call_decl.call_decl_contract_ext))
             && not (is_free call_decl.call_decl_status) ->
          Some (call_decl, body)
      | _ -> None)
  in

  match eligible with
  | [] -> Rewriter.exit_module m
  | _ ->
      let contract_lemma_ident (func_name : Ident.t) : Ident.t =
        Ident.make Loc.dummy ("$" ^ Ident.to_string func_name ^ "_contract") 0
      in

      let* module_qual_ident = Rewriter.current_module_name in

      let* eligible_tbl =
        Rewriter.List.fold_left eligible
          ~init:(Map.empty (module QualIdent))
          ~f:(fun acc (call_decl, _) ->
              let+ func_qual_ident =
                Rewriter.resolve (QualIdent.from_ident call_decl.call_decl_name)
              in
              Map.set acc ~key:func_qual_ident ~data:call_decl)
      in

      (* [current_call_decl] is the func whose companion lemma body is being generated
         (i.e. the "caller"); [callee_decl] is whichever eligible func the call
         resolves to (itself, for self-recursion, or a sibling func also eligible for
         this pass). Delegating to [ext_hooks.rewrite_contract_ext_call] here is how a
         `decreases` clause on a func gets its progress check inserted, piggybacking on
         this auto-lemma mechanism exactly as func bodies have no call-site of their
         own to instrument directly (see WISHLIST.md, "decreases clauses", Phase 1) --
         note this is called for *every* eligible-func call, not just self-recursive
         ones (mirroring [rewrite_contract_ext_calls] above); it's up to the hook
         itself to decide whether caller and callee identity matter to it. *)
      let gen_stmts (current_call_decl : Callable.call_decl) (e : expr) : Stmt.t list Rewriter.t =
        let* current_qual_ident =
          Rewriter.resolve (QualIdent.from_ident current_call_decl.call_decl_name)
        in
        let rec go (acc : Stmt.t list) (e : expr) : Stmt.t list Rewriter.t =
          match e with
          | App (Ite, [ cond; e1; e2 ], _) ->
              let* acc = go acc cond in
              let* then_stmts = go [] e1 in
              let+ else_stmts = go [] e2 in
              Stmt.mk_cond ~loc:(Expr.to_loc e) (Some cond)
                (Stmt.mk_block_stmt ~loc:(Expr.to_loc e1) (List.rev then_stmts))
                (Stmt.mk_block_stmt ~loc:(Expr.to_loc e2) (List.rev else_stmts))
              :: acc
          | App (Var callee, args, _) -> (
              let* acc = Rewriter.List.fold_left args ~init:acc ~f:go in
              match Map.find eligible_tbl callee with
              | None -> Rewriter.return acc
              | Some callee_decl ->
                  let lemma_qual_ident =
                    QualIdent.append module_qual_ident
                      (contract_lemma_ident callee_decl.call_decl_name)
                  in
                  let lemma_call =
                    Stmt.mk_call ~loc:(Expr.to_loc e) ~lhs:[] lemma_qual_ident
                      args ~is_spawn:false
                  in
                  let* ext_hooks = Rewriter.current_ext_hooks in
                  let same_scc_here = same_scc sm current_qual_ident callee in
                  let+ progress_checks =
                    ext_hooks.rewrite_contract_ext_call current_call_decl
                      callee_decl same_scc_here args (Expr.to_loc e)
                  in
                  lemma_call :: (List.fold progress_checks ~init:acc ~f:(fun acc s -> s :: acc)))
          | App (_, args, _) -> Rewriter.List.fold_left args ~init:acc ~f:go
          | Binder _ -> Rewriter.return acc
        in
        let+ stmts = go [] e in
        List.rev stmts
      in

      let* lemma_symbols =
        Rewriter.List.map eligible ~f:(fun (call_decl, body) ->
            let lemma_ident = contract_lemma_ident call_decl.call_decl_name in

            let fn_call_expr =
              Expr.mk_app ~loc:call_decl.call_decl_loc
                ~typ:(Callable.return_type call_decl)
                (Var (QualIdent.from_ident call_decl.call_decl_name))
                (List.map call_decl.call_decl_formals ~f:Expr.from_var_decl)
            in

            let ret_subst_map =
              match call_decl.call_decl_returns with
              | [ r ] ->
                  Map.singleton
                    (module QualIdent)
                    (QualIdent.from_ident r.var_name)
                    fn_call_expr
              | rs ->
                  List.foldi rs
                    ~init:(Map.empty (module QualIdent))
                    ~f:(fun i acc r ->
                        Map.set acc
                          ~key:(QualIdent.from_ident r.var_name)
                          ~data:(Expr.mk_tuple_lookup fn_call_expr i))
            in

            (* Encode the func's own requires clauses as the antecedent of a single implication,
               rather than as actual requires clauses on the lemma: this way, the lemma is
               unconditionally callable (no precondition to discharge at each call site,
               including the recursive ones), and the induction hypothesis obtained from a
               recursive/mutually-recursive call is itself the implication `pre(args) ==>
               post(args, callee(args))`. *)
            let pre_conj =
              Expr.mk_and
                (List.map call_decl.call_decl_precond ~f:(fun pre -> pre.spec_form))
            in
            let post_conj =
              Expr.mk_and
                (List.map call_decl.call_decl_postcond ~f:(fun post ->
                     Expr.alpha_renaming post.spec_form ret_subst_map))
            in
            let postcond_error _ loc =
              ( Error.Verification, loc,
                "The postcondition of " ^ Ident.to_string call_decl.call_decl_name
                ^ " may not hold" )
            in
            let lemma_postconds =
              [ Stmt.mk_spec ~spec_error:[ postcond_error ]
                  (Expr.mk_impl pre_conj post_conj) ]
            in

            let lemma_call_decl =
              Callable.
                {
                  call_decl_kind = Lemma;
                  call_decl_name = lemma_ident;
                  call_decl_formals = call_decl.call_decl_formals;
                  call_decl_returns = [];
                  call_decl_locals = [];
                  call_decl_precond = [];
                  call_decl_postcond = lemma_postconds;
                  call_decl_contract_ext = [];
                  call_decl_status = NotFree;
                  call_decl_is_auto = true;
                  (* Created in `rewrites_phase_3`, after
                     `Masks.compute_masks`/atomicity analysis have already
                     run, so this never goes through the mask fixpoint and
                     `call_decl_needs_mask` would otherwise be stuck at `None`
                     forever. Safe to seed it as `Some []` directly: this
                     lemma's body only ever mirrors a `func`'s (pure
                     expression) body and calls other such auto-lemmas (see
                     the doc comment above), so, transitively, it can never
                     unfold an invariant or need a real mask requirement. *)
                  call_decl_needs_mask = Some [];
                  call_decl_grants_mask = Some [];
                  call_decl_loc = call_decl.call_decl_loc;
               call_decl_loc_params = [];
                }
            in

            let+ lemma_body_stmts = gen_stmts call_decl body in
            let lemma_body =
              Stmt.mk_block_stmt ~loc:call_decl.call_decl_loc lemma_body_stmts
            in

            Module.CallDef
              Callable.
                {
                  call_decl = lemma_call_decl;
                  call_def = ProcDef { proc_body = Some lemma_body };
                })
      in

      let* _ =
        Rewriter.introduce_typecheck_symbols ~loc:m.mod_decl.mod_decl_loc
          ~f:Typing.process_symbol lemma_symbols
      in

      Rewriter.exit_module m


let rewrite_introduce_heaps (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m ->
      m "Rewrites.rewrite_introduce_heaps: Introducing heaps in callable: %a"
        Ident.pr c.call_decl.call_decl_name);
  match c.call_def with
  | FuncDef _ -> Rewriter.return c
  | ProcDef { proc_body = None } -> Rewriter.return c
  | ProcDef { proc_body = Some body } ->
      let* preds_list = ProgUtils.stmt_preds_mentioned body in
      let* ext_hooks = Rewriter.current_ext_hooks in
      let fields_list =
        Stmt.make_stmt_fields_accessed
          ~basic_stmt_ext_fields_accessed:ext_hooks.basic_stmt_ext_fields_accessed
          ~stmt_ext_fields_accessed:ext_hooks.stmt_ext_fields_accessed body
      in
      let au_preds_list = Set.to_list (Stmt.stmt_au_preds_referenced body) in

      Logs.debug (fun m ->
          m "Rewrites.rewrite_introduce_heaps: Predicates mentioned in the body");

      let* body =
        HeapsExplicitTrnsl.introduce_heaps_in_stmts
          ~loc:c.call_decl.call_decl_loc ~fields_list ~preds_list ~au_preds_list
          body
      in

      Rewriter.return { c with call_def = ProcDef { proc_body = Some body } }

let rec rewrite_ssa_stmts (s : Stmt.t) :
    (Stmt.t, var_decl ident_map) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let* var_map = Rewriter.current_user_state in
  let subst_map =
    Map.map var_map ~f:(fun var_decl -> Expr.from_var_decl var_decl)
  in
  let subst_map =
    (Map.map_keys_exn (module QualIdent)) subst_map ~f:(fun ident ->
        QualIdent.from_ident ident)
  in

  match s.stmt_desc with
  | Basic basic_stmt -> (
      match basic_stmt with
      | Spec (spec_kind, spec) ->
          let spec_form = Expr.alpha_renaming spec.spec_form subst_map in

          Rewriter.return
            Stmt.
              {
                s with
                stmt_desc = Basic (Spec (spec_kind, { spec with spec_form }));
              }
      | Assign assign_stmt ->
          let assign_rhs =
            Expr.alpha_renaming assign_stmt.assign_rhs subst_map
          in
          let* assign_lhs =
            if assign_stmt.assign_is_init then
              Rewriter.return assign_stmt.assign_lhs
            else
              Rewriter.List.map assign_stmt.assign_lhs ~f:(fun qual_ident ->
                  let* var_map = Rewriter.current_user_state in

                  let local_var = QualIdent.to_ident qual_ident in

                    let* () = Rewriter.Logs.debug (fun printers m ->
                        m
                          "Rewrites.rewrite_ssa_stmts: Assigning to local \
                          variable %a; for stmt %a"
                          Ident.pr local_var printers.pr_stmt s) in
                    let old_var_decl = Map.find_exn var_map local_var in
                    let new_var_decl =
                      Type.
                        {
                          old_var_decl with
                          var_name =
                            Ident.fresh old_var_decl.var_loc
                              old_var_decl.var_name.ident_name;
                        }
                    in

                    let* _ =
                      Rewriter.introduce_symbol
                        (VarDef { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
                    in

                    let var_map =
                      Map.set var_map ~key:local_var ~data:new_var_decl
                    in

                    let+ _ = Rewriter.set_user_state var_map in

                    QualIdent.from_ident new_var_decl.var_name)
          in

          Rewriter.return
            Stmt.
              {
                s with
                stmt_desc =
                  Basic (Assign { assign_stmt with assign_lhs; assign_rhs });
              }
      | Havoc hvc ->
          if not (QualIdent.is_local hvc.havoc_var) then 
            assert false
          else (
            if hvc.havoc_is_init then
              Rewriter.return (Stmt.mk_skip ~loc:s.stmt_loc)
            else
              let local_var = QualIdent.to_ident hvc.havoc_var in

              Logs.debug (fun m ->
                  m "Rewrites.rewrite_ssa_stmts: Havocing local variable %a"
                    Ident.pr local_var);
              let old_var_decl = Map.find_exn var_map local_var in
              let new_var_decl =
                {
                  old_var_decl with
                  var_name =
                    Ident.fresh old_var_decl.var_loc
                      old_var_decl.var_name.ident_name;
                }
              in

              let* _ =
                Rewriter.introduce_symbol
                  (VarDef { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
              in

              let var_map = Map.set var_map ~key:local_var ~data:new_var_decl in

              let+ _ = Rewriter.set_user_state var_map in

              Stmt.mk_block_stmt ~loc:s.stmt_loc []
            )

      | Bind bind_stmt ->
          let* bind_lhs =
            Rewriter.List.map bind_stmt.bind_lhs ~f:(fun qual_ident ->
                let* var_map = Rewriter.current_user_state in

                let local_var = QualIdent.unqualify qual_ident in

                  let old_var_decl = Map.find_exn var_map local_var in
                  let new_var_decl =
                    Type.
                      {
                        old_var_decl with
                        var_name =
                          Ident.fresh old_var_decl.var_loc
                            old_var_decl.var_name.ident_name;
                      }
                  in

                  let* _ =
                    Rewriter.introduce_symbol
                      (VarDef { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
                  in

                  let var_map =
                    Map.set var_map ~key:local_var ~data:new_var_decl
                  in

                  let+ _ = Rewriter.set_user_state var_map in

                  QualIdent.from_ident new_var_decl.var_name)
          in

          let* var_map = Rewriter.current_user_state in
          let subst_map =
            Map.map var_map ~f:(fun var_decl -> Expr.from_var_decl var_decl)
          in
          let subst_map =
            (Map.map_keys_exn (module QualIdent)) subst_map ~f:(fun ident ->
                QualIdent.from_ident ident)
          in

          let spec_form = Expr.alpha_renaming bind_stmt.bind_rhs.spec_form subst_map in
          let bind_rhs = { bind_stmt.bind_rhs with spec_form } in
          
          Rewriter.return
            Stmt.{ s with stmt_desc = Basic (Bind { bind_lhs; bind_rhs }) }
      | _ ->
          let* () = Rewriter.Logs.debug (fun printers m ->
              m "Rewrites.rewrite_ssa_stmts: Skipping statement %a" printers.pr_stmt s) in
          assert false)
  | Block block_stmt ->
      let+ block_body =
        Rewriter.List.map block_stmt.block_body ~f:rewrite_ssa_stmts
      in

      Stmt.mk_block_stmt ~kind:block_stmt.block_kind ~loc:s.stmt_loc
        block_body
      (* { s with stmt_desc = Block { block_stmt with block_body; } } *)
  | Cond cond_stmt when not cond_stmt.cond_if_assumes_false ->
      let cond_test =
        Option.map
          ~f:(fun test -> Expr.alpha_renaming test subst_map)
          cond_stmt.cond_test
      in

      let* cond_then = rewrite_ssa_stmts cond_stmt.cond_then in

      let* cond_then_map = Rewriter.current_user_state in

      let* _ = Rewriter.set_user_state var_map in
      let* cond_else = rewrite_ssa_stmts cond_stmt.cond_else in

      let* cond_else_map = Rewriter.current_user_state in

      let updated_vals =
        Map.fold2 cond_then_map cond_else_map ~init:[] ~f:(fun ~key ~data acc ->
            match data with
            | `Both (then_var_decl, else_var_decl) ->
                if
                  Ident.(
                    Type.(then_var_decl.var_name)
                    = Type.(else_var_decl.var_name))
                then acc
                else key :: acc
            | `Left _ | `Right _ ->
                Error.error s.stmt_loc
                  "Mismatched variable declarations in then and else branches.")
      in

      let* new_var_map =
        Rewriter.List.fold_left updated_vals ~init:var_map ~f:(fun map var ->
            let old_var_decl = Map.find_exn var_map var in
            let new_var_decl =
              {
                old_var_decl with
                var_name =
                  Ident.fresh old_var_decl.var_loc
                    old_var_decl.var_name.ident_name;
              }
            in

            let+ _ =
              Rewriter.introduce_symbol
                (VarDef { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
            in

            Map.set map ~key:var ~data:new_var_decl)
      in

      let cond_then_assigns =
        List.map updated_vals ~f:(fun var ->
            let old_var_decl = Map.find_exn cond_then_map var in
            let new_var_decl = Map.find_exn new_var_map var in

            Stmt.mk_assign ~loc:s.stmt_loc
              [ QualIdent.from_ident new_var_decl.var_name ]
              (Expr.from_var_decl old_var_decl))
      in

      let cond_then =
        Stmt.mk_block_stmt ~loc:s.stmt_loc (cond_then :: cond_then_assigns)
      in

      let cond_else_assigns =
        List.map updated_vals ~f:(fun var ->
            let old_var_decl = Map.find_exn cond_else_map var in
            let new_var_decl = Map.find_exn new_var_map var in

            Stmt.mk_assign ~loc:s.stmt_loc
              [ QualIdent.from_ident new_var_decl.var_name ]
              (Expr.from_var_decl old_var_decl))
      in

      let cond_else =
        Stmt.mk_block_stmt ~loc:s.stmt_loc (cond_else :: cond_else_assigns)
      in

      let+ _ = Rewriter.set_user_state new_var_map in

      Stmt.
        {
          s with
          stmt_desc =
            Cond
              { cond_test; cond_then; cond_else; cond_if_assumes_false = false };
        }
  | Cond cond_stmt ->
      assert cond_stmt.cond_if_assumes_false;
      assert (
        Poly.(
          cond_stmt.cond_else.stmt_desc
          = Block { block_kind = Regular; block_body = [] }));

      let* orig_map = Rewriter.current_user_state in

      let cond_test =
        Option.map
          ~f:(fun test -> Expr.alpha_renaming test subst_map)
          cond_stmt.cond_test
      in

      let* cond_then = rewrite_ssa_stmts cond_stmt.cond_then in
      let* cond_else = rewrite_ssa_stmts cond_stmt.cond_else in

      let* _ = Rewriter.set_user_state orig_map in

      Rewriter.return
        Stmt.
          {
            s with
            stmt_desc =
              Cond
                {
                  cond_test;
                  cond_then;
                  cond_else;
                  cond_if_assumes_false = true;
                };
          }
  | Loop loop_stmt -> assert false
  | StmtExt _ -> assert false

let rewrite_ssa_transform (c : Callable.t) :
    (Callable.t, var_decl ident_map) Rewriter.t_ext =
  let open Rewriter.Syntax in
  match c.call_def with
  | FuncDef _ | ProcDef { proc_body = None } -> Rewriter.return c
  | ProcDef { proc_body = Some body } ->
      let* () = Rewriter.Logs.debug (fun printers m -> m "rewrite_ssa_transform: init_map: %a" (Util.Print.pr_list_comma printers.pr_type_var_decl) (c.call_decl.call_decl_formals @ c.call_decl.call_decl_returns
         @ c.call_decl.call_decl_locals) ) in

      let init_map =
        List.fold
          (c.call_decl.call_decl_formals @ c.call_decl.call_decl_returns
         @ c.call_decl.call_decl_locals)
          ~init:(Map.empty (module Ident))
          ~f:(fun map var_decl ->
            Map.add_exn map ~key:var_decl.var_name ~data:var_decl)
      in

      let* _ = Rewriter.set_user_state init_map in

      let* () = Rewriter.Logs.debug (fun printers m ->
          m "Rewrites.rewrite_ssa_transform: Starting rewrites on callable %a"
            printers.pr_callable c) in

      let+ body = rewrite_ssa_stmts body in

      { c with call_def = ProcDef { proc_body = Some body } }

let rec rewrite_assign_stmts (s : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  let* () = Rewriter.Logs.debug (fun printers m ->
      m "Rewrites.rewrite_assign_stmts: Starting rewrites on statement %a"
        printers.pr_stmt s) in

  match s.stmt_desc with
  | Basic (Assign assign_stmt) ->
    let+ assign_lhs =
      Rewriter.List.map assign_stmt.assign_lhs ~f:(fun qual_ident ->
          let* qual_ident, symbol =
            Rewriter.resolve_and_find qual_ident
          in
          let+ symbol = Rewriter.Symbol.reify symbol in
          match symbol with
          | VarDef { var_decl; _ } ->
            Expr.mk_var ~typ:var_decl.var_type qual_ident 
          | _ -> assert false
        )
    in

    let assume_stmt =
      Stmt.mk_assume_expr ~loc:s.stmt_loc
        (Expr.mk_eq
           (Expr.mk_tuple assign_lhs)
           assign_stmt.assign_rhs)
    in

    assume_stmt
  | _ ->
      let* s = Rewriter.Stmt.descend s ~f:rewrite_assign_stmts in

      Rewriter.return s


let print_intermediate_state m log_file_name: unit =
  let front_end_out_chan =
    Stdio.Out_channel.create log_file_name
  in

  let formatter_out_chan = Stdlib.Format.formatter_of_out_channel front_end_out_chan in

  Stdlib.Format.fprintf formatter_out_chan
  "%a\n %!" Ast.Module.pr m



let rec rewrites_phase_1 (m : Module.t) : (Module.t * scc_map) Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m -> m "Rewrites.all_rewrites: Starting rewrites");

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_callable_error_msg on module \
         %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_callable_error_msg m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_compr_expr on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_compr_expr m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_set_diff_and_choose_expr on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_set_diff_and_choose_expr m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_loops on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_loops m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Computing call-graph SCCs on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  (* Computed here, right after [rewrite_loops], so synthesized tail-recursive
     loop-procs are already graph vertices; threaded explicitly (not via
     [Rewriter]'s monadic state) all the way to [rewrites_phase_3], since that runs
     as a separate [Rewriter.eval] call in [process_module] and monadic state does
     not survive across those. *)
  let* tbl_after_loops = Rewriter.get_table in
  let scc_map = build_scc_map tbl_after_loops m in
  let* () = check_contract_ext_group_compatibility tbl_after_loops scc_map in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_callable_entries on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_callable_entries m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_contract_ext_calls on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:(rewrite_contract_ext_calls scc_map) m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_inline_preds_expr on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:(rewrite_inline_preds_expr (Set.empty (module QualIdent))) m in

  Rewriter.return (m, scc_map)

let rec rewrites_phase_2 (m : Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_atomic_callable_token on \
         module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables ~f:rewrite_atomic_callable_token m
  in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_atomicity_analysis on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables
      ~f:AtomicityAnalysis.rewrite_atomicity_analysis m
  in

  Rewriter.return m

let rec rewrites_phase_3 (sm : scc_map) (m : Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_add_func_contract_lemmas on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = rewrite_add_func_contract_lemmas sm m in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_fold_unfold_stmts on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_fold_unfold_stmts m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_call_stmts on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_call_stmts m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_ret_stmts on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_ret_stmts m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_frac_field_types on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rec_rewrite_symbols ~f:rewrite_frac_field_types m in

  let* () = Rewriter.Logs.debug (fun _ m1 ->
      m1 "Rewrites.all_rewrites: Starting canonicalize_symbols on module %a"
        Ident.pr m.mod_decl.mod_decl_name) in
  let* m = Rewriter.Module.rewrite_expressions ~f:canonicalize_symbols m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_own_expr_4_arg on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_own_expr_4_arg m in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_new_fpu_stmt_heap_arg on \
         module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_new_fpu_stmt_heap_arg m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_new_stmts on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_new_stmts m in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_add_predicate_validity_lemmas \
         on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables ~f:rewrite_add_predicate_validity_lemmas m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_callable_pre_post_conds on \
         module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables ~f:rewrite_callable_pre_post_conds m
  in

  Logs.debug (fun m1 ->
    m1 "Rewrites.all_rewrites: Starting rewrite_add_pred_implicit_args on module %a"
      Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_expressions ~f:rewrite_add_pred_implicit_args m 
  in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_add_field_utils on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rec_rewrite_symbols
      ~f:HeapsExplicitTrnsl.rewrite_add_field_utils m
  in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_add_pred_utils on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables
      ~f:HeapsExplicitTrnsl.rewrite_add_pred_utils m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_add_atomics_utils on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables
      ~f:HeapsExplicitTrnsl.rewrite_add_atomics_utils m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewriter_skolemize_inhale_stmts on \
         module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_skolemize_inhale_stmts m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting \
         rewriter_user_annot_elim_exists_from_exhales on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.eval_with_user_state ~init:None
      (Rewriter.Module.rewrite_stmts
         ~f:
           HeapsExplicitTrnsl.TrnslExhale
           .rewriter_user_annot_elim_exists_from_exhales m)
  in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_introduce_heaps on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_introduce_heaps m in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewriter_eliminate_binds_for_inhale \
         on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.eval_with_user_state ~init:None
      (Rewriter.Module.rewrite_stmts
         ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale m)
  in

  Logs.debug (fun m1 ->
    m1
      "Rewrites.all_rewrites: Starting rewrite_fpu \
       on module %a"
      Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_fpu m in

  Logs.debug (fun m1 ->
    m1
      "Rewrites.all_rewrites: Starting rewrite_binds \
       on module %a"
      Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_binds m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewriter_skolemize_assume_stmts on \
         module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_skolemize_assume_stmts m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting \
         rewriter_find_witness_elim_exists_from_exhale on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:
        HeapsExplicitTrnsl.TrnslExhale
        .rewriter_find_witness_elim_exists_from_exhale m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_make_heaps_explicit on module \
         %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:HeapsExplicitTrnsl.rewrite_make_heaps_explicit m
  in

  Logs.debug (fun m1 ->
    m1
      "Rewrites.all_rewrites: Starting rewrite_expand_types \
       on module %a"
      Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_types ~f:rewrite_expand_types m in

  let* () = Rewriter.Logs.debug (fun printers m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_ssa_transform on module %a: %a"
        Ident.pr m.mod_decl.mod_decl_name printers.pr_module m) in
  let* m =
    Rewriter.eval_with_user_state
      ~init:(Map.empty (module Ident))
      (Rewriter.Module.rewrite_callables ~f:rewrite_ssa_transform m)
  in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_assign_stmts on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_assign_stmts m in

  let* tbl = Rewriter.get_table in

  (* Logs.debug (fun m -> m "Rewrites.all_rewrites: SymbolTbl Symbols: \n%a\n" (Util.Print.pr_list_comma (fun ppf (k,v) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k Module.pr_symbol v)) (Map.to_alist (Map.filter_keys tbl.tbl_symbols ~f:(fun k -> Poly.((QualIdent.to_string k) = "$Program.pr"))))); *)
  Rewriter.return m

let rewrites_type_ext (m: Module.t) : Module.t Rewriter.t =
  Logs.debug (fun m1 ->
  m1 "Rewrites.rewrites_expr_ext: Starting rewrites_type_ext on module %a"
    Ident.pr m.mod_decl.mod_decl_name);

  let open Rewriter.Syntax in
  let rec rewrite_type_ext (type_expr : type_expr) : type_expr Rewriter.t =
    let* type_expr = Rewriter.Type.descend type_expr ~f:rewrite_type_ext in
    match type_expr with
    | App (TypeExt type_ext, args, type_attr) ->
      let* ext_hooks = Rewriter.current_ext_hooks in
      ext_hooks.rewrite_type_ext type_ext args (Type.to_loc type_expr)
    | _ -> Rewriter.return type_expr

  in
  let* m =
    Rewriter.Module.rewrite_types ~f:rewrite_type_ext m in

  Rewriter.return m

let rewrites_expr_ext (m: Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in
  let rec rewrite_expr_ext  (expr : expr) : expr Rewriter.t =
    let* expr = Rewriter.Expr.descend expr ~f:rewrite_expr_ext in
    match expr with
    | App (ExprExt expr_ext, args, expr_attr) ->
      let* ext_hooks = Rewriter.current_ext_hooks in
      ext_hooks.rewrite_expr_ext expr_ext args expr_attr
    | _ -> Rewriter.Expr.descend expr ~f:rewrite_expr_ext
  in

  Logs.debug (fun m1 ->
  m1 "Rewrites.rewrites_expr_ext: Starting rewrites_expr_ext on module %a"
    Ident.pr m.mod_decl.mod_decl_name);

  let* m = 
    Rewriter.Module.rewrite_expressions ~f:rewrite_expr_ext m in

  Rewriter.return m

let rewrites_stmt_ext (m: Module.t) : Module.t Rewriter.t =
  Logs.debug (fun m1 ->
  m1 "Rewrites.rewrites_stmt_ext: Starting rewrites_stmt_ext on module %a"
    Ident.pr m.mod_decl.mod_decl_name);

  let open Rewriter.Syntax in
  let rec rewrite_stmt_ext  (stmt : Stmt.t) : Stmt.t Rewriter.t =
    match stmt.stmt_desc with
    | Basic (BasicStmtExt (stmt_ext, args)) ->
      let* ext_hooks = Rewriter.current_ext_hooks in
      ext_hooks.rewrite_basic_stmt_ext stmt_ext args (Stmt.to_loc stmt)
    | StmtExt stmt_ext ->
      let* ext_hooks = Rewriter.current_ext_hooks in
      ext_hooks.rewrite_stmt_ext stmt_ext (Stmt.to_loc stmt)
    | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_stmt_ext

  in
  let* m = 
    Rewriter.Module.rewrite_stmts ~f:rewrite_stmt_ext m in

  Rewriter.return m

let process_module ?(tbl = SymbolTbl.create ()) ?ext_hooks ?cli_config (m : Module.t) =
  assert (SymbolTbl.curr_is_root tbl);

  (* assert Ident.(m.mod_decl.mod_decl_name = QualIdent.to_ident (SymbolTbl.root_ident tbl)); *)
  let tbl, (m, scc_map) = Rewriter.eval ?ext_hooks ?cli_config (rewrites_phase_1 m) tbl in

  let tbl, m = Rewriter.eval ?ext_hooks ?cli_config (Masks.compute_masks m) tbl in

  let tbl, m = Rewriter.eval ?ext_hooks ?cli_config (Masks.check_no_interface_reach_back m) tbl in

  let tbl, m = Rewriter.eval ?ext_hooks ?cli_config (rewrites_phase_2 m) tbl in

  let tbl, m = Rewriter.eval ?ext_hooks ?cli_config (rewrites_type_ext m) tbl in
  let tbl, m = Rewriter.eval ?ext_hooks ?cli_config (rewrites_expr_ext m) tbl in
  let tbl, m = Rewriter.eval ?ext_hooks ?cli_config (rewrites_stmt_ext m) tbl in

  (* Logs.debug (fun m -> m "Rewrites.process_module: whoop-di-doo, here we go again"); *)

  let tbl, m = Rewriter.eval ?ext_hooks ?cli_config (rewrites_type_ext m) tbl in
  let tbl, m = Rewriter.eval ?ext_hooks ?cli_config (rewrites_expr_ext m) tbl in
  let tbl, m = Rewriter.eval ?ext_hooks ?cli_config (rewrites_stmt_ext m) tbl in

  let tbl, m = Rewriter.eval ?ext_hooks ?cli_config (rewrites_phase_3 scc_map m) tbl in

  (tbl, m)

module ProgStats = struct
  type prog_stats = {
    prog_decls: int;
    proof_decls: int;
    prog_instr: int;
    proof_pred_instr: int;
    proof_inv_instr: int;
    proof_au_instr: int;
    proof_remaining_instr: int; 
    spec_count: int;
  }

  let pr ppf prog_stats =
    let open Stdlib.Format in
    fprintf ppf
"Program Declarations: %d
Proof Declarations: %d
Program Instructions: %d
Proof Instructions: %d
    Proof Predicate Instructions: %d
    Proof Invariant Instructions: %d
    Proof Atomicity Instructions: %d
    Proof Remaining Instructions: %d
Specification Count: %d"
      prog_stats.prog_decls 
      prog_stats.proof_decls 
      prog_stats.prog_instr
      (prog_stats.proof_pred_instr + prog_stats.proof_inv_instr + prog_stats.proof_au_instr + prog_stats.proof_remaining_instr)
      prog_stats.proof_pred_instr 
      prog_stats.proof_inv_instr
      prog_stats.proof_au_instr 
      prog_stats.proof_remaining_instr
      prog_stats.spec_count

  let init_prog_stats = {
    prog_decls = 0;
    proof_decls = 0;
    prog_instr = 0;
    proof_pred_instr = 0;
    proof_inv_instr = 0;
    proof_au_instr = 0;
    proof_remaining_instr = 0; 
    spec_count = 0;
  }

  let merge_prog_stats ps1 ps2 =
  {
    prog_decls = ps1.prog_decls + ps2.prog_decls;
    proof_decls = ps1.proof_decls + ps2.proof_decls;
    prog_instr = ps1.prog_instr + ps2.prog_instr;
    proof_pred_instr = ps1.proof_pred_instr + ps2.proof_pred_instr;
    proof_inv_instr = ps1.proof_inv_instr + ps2.proof_inv_instr;
    proof_au_instr = ps1.proof_au_instr + ps2.proof_au_instr;
    proof_remaining_instr = ps1.proof_remaining_instr + ps2.proof_remaining_instr;
    spec_count = ps1.spec_count + ps2.spec_count;
  }

  let rec computeStats md : prog_stats Rewriter.t =
    let open Rewriter.Syntax in
    let* _ = Rewriter.enter_module md in
    let* prog_stats = Rewriter.List.fold_left md.Module.mod_def ~init:init_prog_stats ~f:(fun ps instr ->
      match instr with
      | Import _ -> Rewriter.return ps
      | SymbolDef s -> 
        let+ symbolStats = computeSymbolStats s in
        merge_prog_stats ps symbolStats
    ) in 
    let+ _ = Rewriter.exit_module md in

    prog_stats

  and computeSymbolStats s : prog_stats Rewriter.t =
    match s with
    | ModDef md ->
      if is_free md.mod_decl.mod_decl_status then
        Rewriter.return init_prog_stats
      else
        computeStats md
    | ModInst _ | TypeDef _ -> Rewriter.return { init_prog_stats with proof_decls = 1; }
    | VarDef _ -> 
      Rewriter.return { init_prog_stats with 
        (* prog_decls = 1;  *)
        proof_decls = 1; 
      }
    | FieldDef f -> Rewriter.return @@
      if f.field_is_ghost then
        { init_prog_stats with proof_decls = 1; }
      else
        { init_prog_stats with prog_decls = 1; }
    | CallDef c ->
      computeCallableStats c
    | _ -> Rewriter.return init_prog_stats

  and computeCallableStats c : prog_stats Rewriter.t =
    let open Rewriter.Syntax in 

    if is_free c.call_decl.call_decl_status then
      Rewriter.return init_prog_stats
    else

    let callable_prog_stats = 
      let call_kind = c.call_decl.call_decl_kind in

      match call_kind with
      | Proc ->
        { init_prog_stats with 
          prog_decls = 1;
          (* spec_count = List.length (c.call_decl.call_decl_precond @ c.call_decl.call_decl_postcond); *)
          spec_count = 
            if List.is_empty (c.call_decl.call_decl_precond @ c.call_decl.call_decl_postcond) then 0 else 1;
        }
      | Lemma ->
        { init_prog_stats with
          proof_decls = 1;
          spec_count = 
            if List.is_empty (c.call_decl.call_decl_precond @ c.call_decl.call_decl_postcond) then 0 else 1
        }
      | Func ->
        { init_prog_stats with 
          (* prog_decls = 1; *)
          proof_decls = 1;
          (* spec_count = List.length (c.call_decl.call_decl_precond @ c.call_decl.call_decl_postcond); *)
          spec_count = 
            if List.is_empty (c.call_decl.call_decl_precond @ c.call_decl.call_decl_postcond) then 0 else 1;
        }
      | Pred | Invariant ->
        { init_prog_stats with 
          proof_decls = 1;
          spec_count = 0;
        }
    in

    match c.call_def with
    | FuncDef _ -> Rewriter.return callable_prog_stats
    | ProcDef pr ->
      match pr.proc_body with
      | None -> Rewriter.return callable_prog_stats
      | Some s ->
        let+ stmt_stats = computeStmtStats s c.call_decl in
        merge_prog_stats callable_prog_stats stmt_stats

  and computeStmtStats s proc_decl : prog_stats Rewriter.t = 
    let open Rewriter.Syntax in
    match s.Stmt.stmt_desc with
    | Stmt.Block block_desc -> 
        Rewriter.List.fold_left block_desc.block_body ~init:init_prog_stats ~f:(fun ps s -> 
          let+ stmt_stats = computeStmtStats s proc_decl in
          merge_prog_stats ps stmt_stats)

    | Basic b -> computeBasicStmtStats b proc_decl
    | Loop loop_desc -> 
      let loop_stats = {init_prog_stats with 
        prog_instr = 1; 
        (* spec_count = List.length loop_desc.loop_contract; *)
        spec_count = 
          if List.is_empty loop_desc.loop_contract then 0 else 1;
      } in

      let+ body_stats = computeStmtStats loop_desc.loop_postbody proc_decl in
      merge_prog_stats loop_stats body_stats

    | Cond cond_desc -> 
      let* cond_if_stats = computeStmtStats cond_desc.cond_then proc_decl in
      let+ cond_else_stats = computeStmtStats cond_desc.cond_else proc_decl in

      let cond_stats = {init_prog_stats with 
        prog_instr = 
          if (cond_if_stats.prog_instr > 0 || cond_else_stats.prog_instr > 0) 
            then 1 
          else 0  
        ; 
      } in

      merge_prog_stats cond_stats
        (merge_prog_stats cond_if_stats cond_else_stats)

    | StmtExt _ -> Rewriter.return init_prog_stats

  and computeBasicStmtStats b proc_decl : prog_stats Rewriter.t =
    let open Rewriter.Syntax in
    let* printers = Rewriter.current_printers in

    (* Logs.debug (fun m ->m 
      "ProgStats: basic_stmt: %a"
      Stmt.pr_basic_stmt b
    ); *)
    match b with
    | Stmt.VarDef _ | Havoc _ | AUAction {auaction_kind = BindAU _;} ->
      Rewriter.return init_prog_stats

    | Assign assign_desc -> 
      let+ is_ghost = 
        Rewriter.List.fold_left ~init:false assign_desc.assign_lhs ~f:(fun b qi ->
          let local_vars = proc_decl.call_decl_locals @ proc_decl.call_decl_returns in
          let local_vd_optn = 
            List.find local_vars ~f:(
              fun vd -> 
                Ident.(vd.var_name = QualIdent.to_ident qi)
            )
          in

          let+ v_decl = 
            match local_vd_optn with
            | Some vd -> Rewriter.return vd
            | None ->
              let+ v_def = Rewriter.find_and_reify_var qi in 
              v_def.var_decl
          in
            b || v_decl.var_ghost
        )
      in

      if is_ghost 
        then { init_prog_stats with proof_remaining_instr = 1; }
      else
        let _ = Logs.debug (fun m -> m "prog_instr: %a" printers.pr_stmt_basic b) in
        { init_prog_stats with prog_instr = 1; }

    | New new_desc ->
      let+ (is_ghost, is_concrete) = Rewriter.List.fold_left ~init:(false, false) new_desc.new_args ~f:(fun (b1, b2) (qi, _) ->
        Logs.debug (fun m -> m "Rewrites.ProgStats.computeBasicStmtStats: new_desc field = %a" QualIdent.pr qi);
        let+ field_decl = Rewriter.find_and_reify_field qi in
        b1 || field_decl.field_is_ghost, b2 || not field_decl.field_is_ghost
      )
      in

      if is_ghost && is_concrete then
        let _ = Logs.debug (fun m -> m "prog_instr: %a" printers.pr_stmt_basic b) in
        { init_prog_stats with prog_instr = 1; proof_remaining_instr = 1; }
      else if is_ghost then
        { init_prog_stats with proof_remaining_instr = 1; }
      else
        let _ = Logs.debug (fun m -> m "prog_instr: %a" printers.pr_stmt_basic b) in
        { init_prog_stats with prog_instr = 1; }
    
    | FieldRead field_read_desc ->
      let+ field_def = Rewriter.find_and_reify_field field_read_desc.field_read_field in
      let is_ghost = field_def.field_is_ghost in

      if is_ghost then
        { init_prog_stats with proof_remaining_instr = 1; }
      else 
        let _ = Logs.debug (fun m -> m "prog_instr: %a" printers.pr_stmt_basic b) in
        { init_prog_stats with prog_instr = 1; }
    
    | FieldWrite field_write_desc ->
      let+ field_def = Rewriter.find_and_reify_field field_write_desc.field_write_field in
      let is_ghost = field_def.field_is_ghost in

      if is_ghost then
        { init_prog_stats with proof_remaining_instr = 1; }
      else 
        let _ = Logs.debug (fun m -> m "prog_instr: %a" printers.pr_stmt_basic b) in
        { init_prog_stats with prog_instr = 1; }
    
    | Call call_desc ->
      let+ callable = Rewriter.find_and_reify_callable call_desc.call_name in

      begin match callable.call_decl.call_decl_kind with
      | Lemma -> { init_prog_stats with proof_remaining_instr = 1; }
      | Proc -> 
        let _ = Logs.debug (fun m -> m "prog_instr: %a" printers.pr_stmt_basic b) in
        { init_prog_stats with prog_instr = 1; }
      | _ -> { init_prog_stats with proof_remaining_instr = 1; }
      end
    
    | Return _ -> 
      let _ = Logs.debug (fun m -> m "prog_instr: %a" printers.pr_stmt_basic b) in
      Rewriter.return { init_prog_stats with prog_instr = 1; }

    | Spec _ | Bind _ | Fpu _ -> 
      Rewriter.return { init_prog_stats with proof_remaining_instr = 1; }

    | Use use_desc ->
      let+ use_callable = Rewriter.find_and_reify_callable use_desc.use_name in

      begin match use_callable.call_decl.call_decl_kind with
      | Pred -> 
        { init_prog_stats with proof_pred_instr = 1; }
      | Invariant ->
        { init_prog_stats with proof_inv_instr = 1; }
      | _ ->
        { init_prog_stats with proof_remaining_instr = 1; }
      end
    
    | AUAction _ ->
      Rewriter.return { init_prog_stats with proof_au_instr = 1; }

    | BasicStmtExt (stmt_ext, args) ->
      Rewriter.return { init_prog_stats with prog_instr = 1; }
end

let compute_stats ?ext_hooks tbl m =
  assert (SymbolTbl.curr_is_root tbl);

  let tbl, prog_stats = Rewriter.eval ?ext_hooks (ProgStats.computeStats m) tbl in

  prog_stats
