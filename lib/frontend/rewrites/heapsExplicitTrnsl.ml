open Base
open Ast
open Util
open Frontend

(**
  
  The following grammar of assertion expressions is supported:

        a :=
            e ==> a
            e ? a : a 
            a && a
            a2

        a2 :=
            a2 && a2
            a2'
            forall (x:T)* :: a2

        a2' := 
            a2' && a2'
            e ==> a2'
            e ? a2' : a2'
            a1

        a1 :=
            a1'
            a1 && a1
            exists (x:T)* :: a1

        a1' :=
            a1' && a1'
            e ==> a1'
            e ? a1' : a1'
            a0

        a0 :=
            a0 && a0
            own(e, f, v)
            pred_name( e* )
            e
  *)

type inhale_exhale = Inhale | Exhale
type conditionals = Expr.t list * Expr.t list
type conditions = Expr.t list
(* Two componends in conditionals are used to keep track of conditionals given before existential quants, and ones given after existential quants *)

type universal_quants = {
  univ_vars : (ident * var_decl) list;
  triggers : expr list list;
}

type existential_quant_record = {
  var_decl : var_decl;
  quantified_exprs : (expr * conditionals) list;
}

type existential_quants = existential_quant_record IdentMap.t

let unsupported_expr_error (expr : Expr.t) : 'a =
  Error.error (Expr.to_loc expr)
    ("Unsupported expression under inhale/exhale: " ^ Expr.to_string expr)

let field_heap_name (field_name : qual_ident) =
  let field_name_str = QualIdent.to_string field_name in
  let field_name_str = Rewriter.ProgUtils.serialize field_name_str in
  Ident.make Loc.dummy (field_name_str ^ "$Heap") 0

let field_heap_name2 (field_name : qual_ident) =
  let field_name_str = QualIdent.to_string field_name in
  let field_name_str = Rewriter.ProgUtils.serialize field_name_str in
  Ident.make Loc.dummy (field_name_str ^ "$Heap2") 0

let pred_heap_name (pred_name : qual_ident) =
  let pred_name_str = QualIdent.to_string pred_name in
  let pred_name_str = Rewriter.ProgUtils.serialize pred_name_str in
  Ident.make Loc.dummy (pred_name_str ^ "$Heap") 0

let pred_heap_name2 (pred_name : qual_ident) =
  let pred_name_str = QualIdent.to_string pred_name in
  let pred_name_str = Rewriter.ProgUtils.serialize pred_name_str in
  Ident.make Loc.dummy (pred_name_str ^ "$Heap2") 0

let au_heap_name (callable_name : qual_ident) =
  let callable_name_str = QualIdent.to_string callable_name in
  let callable_name_str = Rewriter.ProgUtils.serialize callable_name_str in
  Ident.make Loc.dummy (callable_name_str ^ "$AU_Heap") 0

let au_heap_name2 (callable_name : qual_ident) =
  let callable_name_str = QualIdent.to_string callable_name in
  let callable_name_str = Rewriter.ProgUtils.serialize callable_name_str in
  Ident.make Loc.dummy (callable_name_str ^ "$AU_Heap2") 0

let generate_injectivity_assertions ~loc (universal_quants : universal_quants)
    (conditions : conditions) (expr : expr) : Stmt.t Rewriter.t =
  (* Running example :
      Say we have:
      forall a, b :: p1(a, b) && p2(a, b) ==> f(a, b)

      universal_quants : { a, b }
      conditions : [ p1(a, b); p2(a, b) ]
      expr : f(a, b)
  *)
  let univ_quants_list = universal_quants.univ_vars in

  (* [a, b] *)
  let univ_vars =
    List.map univ_quants_list ~f:(fun (_, var_decl) -> var_decl)
  in

  (* [a', b'] *)
  let dup_vars =
    List.map univ_quants_list ~f:(fun (_, var_decl) ->
        {
          var_decl with
          var_name = Ident.fresh loc var_decl.var_name.ident_name;
        })
  in

  let alpha_renaming_map =
    List.fold2_exn univ_vars dup_vars
      ~init:(Map.empty (module QualIdent))
      ~f:(fun map old_var_decl new_var_decl ->
        Map.add_exn map
          ~key:(QualIdent.from_ident old_var_decl.var_name)
          ~data:
            (Expr.mk_var ~typ:new_var_decl.var_type
               (QualIdent.from_ident new_var_decl.var_name)))
  in

  (* [p1(a', b'); p2(a', b')] *)
  let renamed_conditions =
    List.map conditions ~f:(fun cond ->
        Expr.alpha_renaming cond alpha_renaming_map)
  in

  (* f(a, b) == f(a', b') *)
  let expr_eq = Expr.mk_eq expr (Expr.alpha_renaming expr alpha_renaming_map) in

  (* [a == a'; b == b']  *)
  let vars_eq_list =
    List.map2_exn univ_vars dup_vars ~f:(fun old_var_decl new_var_decl ->
        Expr.mk_eq
          (Expr.mk_var ~typ:old_var_decl.var_type
             (QualIdent.from_ident old_var_decl.var_name))
          (Expr.mk_var ~typ:new_var_decl.var_type
             (QualIdent.from_ident new_var_decl.var_name)))
  in

  let assert_expr =
    (* forall a, b, a', b' ::
       f(a, b) == f(a', b') && p1(a, b) && p2(a, b) && p1(a', b') && p2(a', b')  ==>
        a == a' && b == b'
    *)
    Expr.mk_binder ~loc ~typ:Type.bool Forall (univ_vars @ dup_vars)
      (Expr.mk_impl
         (Expr.mk_and ((expr_eq :: conditions) @ renamed_conditions))
         (Expr.mk_and vars_eq_list))
  in

  let assert_stmt =
    let error =
      ( Error.Verification,
        loc,
        "Could not prove the injectivity of the index expression for this \
         iterated separating conjunction" )
    in
    Stmt.mk_assert_expr ~loc ~cmnt:("Injectivity assertion: " ^ "universal quants: " ^ String.concat ~sep:", " (List.map univ_vars ~f:(fun v -> Ident.to_string v.var_name)) ^ "; expression: " ^ Expr.to_string expr) 
      ~spec_error:[ Stmt.mk_const_spec_error error ]
      assert_expr
  in

  Rewriter.return assert_stmt

let compute_env_local_var_decls ~loc (expr: expr) (conds: conditions) (universal_quants : universal_quants) : (var_decl list) Rewriter.t =
  let open Rewriter.Syntax in
  let symbols =
    List.fold (expr :: conds)
      ~init:(Set.empty (module QualIdent))
      ~f:(fun symbols cond -> Expr.symbols ~acc:symbols cond)
  in

  let locals =
    let locals_set = 
      Set.filter symbols ~f:(fun s ->
          QualIdent.is_local s
          && not
              (List.exists universal_quants.univ_vars ~f:(fun (i, _) ->
                    Ident.(i = QualIdent.unqualify s))))
    in

    Set.to_list locals_set
  in

  let+ local_var_decls =
    Rewriter.List.map locals ~f:(fun qual_ident ->
        let+ symbol = Rewriter.find_and_reify loc qual_ident in
        match symbol with
        | VarDef v -> v.var_decl
        | _ -> Error.error loc "Expected a variable declaration")
  in

  Logs.debug (fun m -> 
    m 
      "heapsExplicitTrnsl.compute_env_local_var_decls: expr: %a;\n conds: %a;\n universal_quants: %a;\n \
      OUTPUT: local_var_decls: %a"
    Expr.pr expr
    Expr.pr_list conds
    Type.pr_var_decl_list (List.map ~f:snd universal_quants.univ_vars)
    Type.pr_var_decl_list local_var_decls
  );
  local_var_decls

let generate_inv_function ~loc (universal_quants : universal_quants)
    (conds : conditions) (inv_expr : expr) ~(arg_expr : expr) : expr Rewriter.t
    =
  (* Logs.debug (fun m -> m "heapsExplicitTrnsl.generate_inv_function: Generating inv function for %a" Expr.pr inv_expr);
     Logs.debug (fun m -> m "arg_expr: %a" Expr.pr arg_expr);
     Logs.debug (fun m -> m "inv_expr_type: %a; arg_expr_type: %a" Type.pr (Expr.to_type inv_expr) Type.pr (Expr.to_type arg_expr)); *)
  let open Rewriter.Syntax in
  let* tp1 = Typing.ProcessTypeExpr.expand_type_expr (Expr.to_type inv_expr)
  and* tp2 = Typing.ProcessTypeExpr.expand_type_expr (Expr.to_type arg_expr) in

  assert (Type.(tp1 = tp2));

  if List.is_empty universal_quants.univ_vars then Rewriter.return inv_expr
  else
    let inv_fn_ident =
      Ident.fresh loc
        ("$inv_" ^ Rewriter.ProgUtils.serialize (Expr.to_string inv_expr))
    in

    let* env_local_var_decls =
      compute_env_local_var_decls ~loc inv_expr conds universal_quants
    in

    let arg_type = Expr.to_type inv_expr in

    let arg_var_decl =
      let arg_ident = Ident.fresh loc "res" in
      {
        Type.var_name = arg_ident;
        var_loc = loc;
        var_type = arg_type;
        var_const = true;
        var_ghost = false;
        var_implicit = false;
      }
    in

    let formal_var_decls = arg_var_decl :: env_local_var_decls in

    let ret_type =
      Type.mk_prod loc
        (List.map universal_quants.univ_vars ~f:(fun (_, var_decl) ->
             var_decl.var_type))
    in

    let ret_var_decl =
      {
        Type.var_name = Ident.fresh loc "$ret";
        var_loc = loc;
        var_type = ret_type;
        var_const = true;
        var_ghost = false;
        var_implicit = false;
      }
    in

    let univ_vars_exprs =
      List.mapi universal_quants.univ_vars ~f:(fun index (var, var_decl) ->
          Expr.mk_tuple_lookup (Expr.from_var_decl ret_var_decl) index)
    in

    let* precond =
      let+ assert_stmt =
        generate_injectivity_assertions ~loc universal_quants conds inv_expr
      in
      match assert_stmt.stmt_desc with
      | Basic (Spec (Assert, spec)) -> spec
      | _ -> Error.error loc "Expected an assertion statement"
    in

    let postcond =
      let spec_form =
        let var_decls_forall =
          List.map universal_quants.univ_vars ~f:(fun (var, var_decl) ->
              var_decl)
        in
        let var_decls = var_decls_forall in

        let eq_expr = Expr.mk_eq (Expr.from_var_decl arg_var_decl) inv_expr in

        Expr.mk_binder ~loc ~typ:Type.bool Forall var_decls
          (Expr.mk_impl ~loc
             (Expr.mk_and ~loc (eq_expr :: conds))
             (Expr.mk_and
                (List.map2_exn universal_quants.univ_vars univ_vars_exprs
                   ~f:(fun (_, var_decl) expr ->
                     Expr.mk_eq ~loc (Expr.from_var_decl var_decl) expr))))
      in

      Stmt.mk_spec spec_form
    in

    let call_decl =
      {
        Callable.call_decl_kind = Func;
        call_decl_name = inv_fn_ident;
        call_decl_formals = formal_var_decls;
        call_decl_returns = [ ret_var_decl ];
        call_decl_locals = [];
        call_decl_precond = [ precond ];
        call_decl_postcond = [ postcond ];
        call_decl_is_free = false;
        call_decl_is_auto = false;
        call_decl_loc = loc;
        call_decl_mask = Some (Set.empty (module QualIdent));
      }
    in

    let* inv_fn_qual_ident =
      let+ module_qual_ident = Rewriter.current_module_name in

      QualIdent.append module_qual_ident inv_fn_ident
    in

    let fn_def =
      Module.CallDef
        Callable.{ call_decl; call_def = FuncDef { func_body = None } }
    in

    let+ _ = Rewriter.introduce_symbol fn_def in

    Expr.mk_app ~loc ~typ:ret_type (Var inv_fn_qual_ident)
      (arg_expr :: List.map env_local_var_decls ~f:Expr.from_var_decl)


let ident_to_skolem_fn_ident ~loc ident =
  Ident.fresh loc ("$skolem_" ^ Ident.to_string ident)

let generate_skolem_function (universal_quants : universal_quants)
    (var_decl : var_decl) ~skolem_id ?(postconds : expr list = [])
    ?(optn_args : (var_decl * expr) list = []) ~loc : expr Rewriter.t =
  let open Rewriter.Syntax in
  let univ_quants_list = universal_quants.univ_vars in

  let skolem_fn_ident =
    skolem_id
  in

  let formal_var_decls =
    List.map univ_quants_list ~f:(fun (v, v_decl) ->
        {
          Type.var_name = v_decl.var_name;
          var_loc = loc;
          var_type = v_decl.var_type;
          var_const = true;
          var_ghost = false;
          var_implicit = false;
        })
    @ List.map optn_args ~f:(fun (v_decl, _) ->
          {
            Type.var_name = v_decl.var_name;
            var_loc = loc;
            var_type = v_decl.var_type;
            var_const = true;
            var_ghost = false;
            var_implicit = false;
          })
  in

  let ret_var_decl =
    {
      Type.var_name =
        Ident.fresh loc ("ret_" ^ Ident.to_string var_decl.var_name);
      var_loc = loc;
      var_type = var_decl.var_type;
      var_const = true;
      var_ghost = false;
      var_implicit = false;
    }
  in

  let postconds =
    List.map postconds ~f:(fun postcond ->
        Expr.alpha_renaming postcond
          (Map.singleton
             (module QualIdent)
             (QualIdent.from_ident var_decl.var_name)
             (Expr.from_var_decl ret_var_decl)))
  in

  let postconds =
    List.map postconds ~f:(fun postcond -> Stmt.mk_spec postcond)
  in

  let call_decl =
    {
      Callable.call_decl_kind = Func;
      call_decl_name = skolem_fn_ident;
      call_decl_formals = formal_var_decls;
      call_decl_returns = [ ret_var_decl ];
      call_decl_locals = [];
      call_decl_precond = [];
      call_decl_postcond = postconds;
      call_decl_loc = loc;
      call_decl_is_free = false;
      call_decl_is_auto = false;
      call_decl_mask = Some (Set.empty (module QualIdent));
    }
  in

  let* skolem_fn_qual_ident =
    let+ module_qual_ident = Rewriter.current_module_name in

    QualIdent.append module_qual_ident skolem_fn_ident
  in

  let callable =
    Callable.{ call_decl; call_def = FuncDef { func_body = None } }
  in

  let symbol = Module.CallDef callable in

  let* _ =
    Rewriter.introduce_typecheck_symbol ~loc ~f:Frontend.Typing.process_symbol
      symbol
  in

  let ret_expr_args_list =
    List.map univ_quants_list ~f:(fun (_, vd) -> Expr.from_var_decl vd)
    @ List.map optn_args ~f:(fun (_, expr) -> expr)
  in

  let ret_expr =
    Expr.mk_app ~typ:var_decl.var_type (Expr.Var skolem_fn_qual_ident)
      ret_expr_args_list
  in

  (Logs.debug (fun m -> m 
  "heapsExplicitTrnsl.generate_skolem_function: \
    universal_quants: %a \n \
    var_decl: %a \n \
    postconds: %a \n \
    optn_args: %a \n \
    output_expr: %a
  "
    Type.pr_var_decl_list (List.map ~f:snd universal_quants.univ_vars)
    Type.pr_var_decl var_decl
    (Stmt.pr_spec_list "skolemPostConds") postconds
    (Util.Print.pr_list_comma (fun ppf (vd, e) ->
      Stdlib.Format.fprintf ppf "%a -> %a" Type.pr_var_decl vd Expr.pr e
    )) optn_args
    Expr.pr ret_expr
  ));

  Rewriter.return ret_expr



(* This function generates a module which roughly looks like the following:
 *     module f$utils {
 *       type T = f.field_type.T;
 *   
 *       var id : T = f.field_type.id;
 *   
 *       func f$heapValid(h: Map[Ref, T]) returns (ret:Bool) {
 *         forall l: Ref :: T.valid(h[l])
 *       }
 *   
 *       func f$heapChunkComp(x1: T, x2: T) returns (ret: T) {
 *         T.comp(x1, x2)
 *       }
 *   
 *       func f$heapChunkFrame(x1: T, x2: T) returns (ret: T) {
 *         T.frame(x1, x2)
 *       }
 *   
 *       func f$heapchunk_compare(x1: T, x2: T) returns (ret: Bool) {
 *         T.valid(f$heapSubChunk(x1, x2))
 *       }
 *     }
*)
let generate_utils_module ~(is_field : bool) (mod_ident : ident)
    (ra_qual_ident : qual_ident) ?(in_arg_typ = Type.ref) (loc : location) :
    Module.symbol Rewriter.t =
  assert ((not is_field) || (is_field && Type.equal in_arg_typ Type.ref));

  let open Rewriter.Syntax in

  let fld_elem_type = Rewriter.ProgUtils.get_ra_rep_type ra_qual_ident in

  let mod_decl =
    {
      Module.mod_decl_name = mod_ident;
      mod_decl_formals = [];
      mod_decl_returns = None;
      mod_decl_interfaces = Set.empty (module QualIdent);
      mod_decl_rep = None;
      mod_decl_is_ra = false;
      mod_decl_is_interface = false;
      mod_decl_is_free = false;
      mod_decl_loc = loc;
    }
  in

  let* mod_def =
    let type_ident = Rewriter.ProgUtils.heap_utils_rep_type_ident loc in
    let type_tp_expr = Type.mk_var loc (QualIdent.from_ident type_ident) in

    let type_def =
      {
        Module.type_def_name = type_ident;
        type_def_expr = Some fld_elem_type;
        type_def_rep = true;
        type_def_loc = loc;
      }
    in

    let var_def =
      {
        Stmt.var_decl =
          Type.mk_var_decl ~loc ~const:true
            (Rewriter.ProgUtils.heap_utils_id_ident loc)
            type_tp_expr;
        var_init =
          Some
            (Expr.mk_var ~loc ~typ:fld_elem_type
               (Rewriter.ProgUtils.get_ra_id ra_qual_ident));
      }
    in

    let heap_valid_fn_decl =
      {
        Callable.call_decl_kind = Func;
        call_decl_name = Rewriter.ProgUtils.heap_utils_valid_ident loc;
        call_decl_formals =
          [
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "h")
              (Type.mk_map loc in_arg_typ type_tp_expr);
          ];
        call_decl_returns =
          [
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret") Type.bool;
          ];
        call_decl_locals = [];
        call_decl_precond = [];
        call_decl_postcond = [];
        call_decl_is_free = true;
        call_decl_is_auto = false;
        call_decl_loc = loc;
        call_decl_mask = Some (Set.empty (module QualIdent));
      }
    in

    let l_var_decl =
      Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "l") in_arg_typ
    in

    let ra_valid_fn_qual_ident =
      Rewriter.ProgUtils.get_ra_valid_fn_qual_ident ra_qual_ident
    in

    let heap_valid_fn =
      {
        Callable.call_decl = heap_valid_fn_decl;
        call_def =
          FuncDef
            {
              func_body =
                Some
                  (Expr.mk_and
                     (Expr.mk_binder ~loc ~typ:Type.bool Forall [ l_var_decl ]
                        (Expr.mk_app ~loc ~typ:Type.bool
                           (Expr.Var ra_valid_fn_qual_ident)
                           [
                             Expr.mk_maplookup ~loc
                               (Expr.from_var_decl
                                  (List.hd_exn
                                     heap_valid_fn_decl.call_decl_formals))
                               (Expr.from_var_decl l_var_decl);
                           ])
                     ::
                     (if is_field then
                        (* Null has no ownership *)
                        [
                          Expr.mk_eq ~loc
                            (Expr.mk_maplookup ~loc
                               (Expr.from_var_decl
                                  (List.hd_exn
                                     heap_valid_fn_decl.call_decl_formals))
                               (Expr.mk_app ~loc ~typ:Type.ref Null []))
                            (Expr.mk_var ~loc ~typ:type_tp_expr
                               (Rewriter.ProgUtils.get_ra_id ra_qual_ident));
                        ]
                      else [])));
            };
      }
    in

    let heap_add_chunk_fn_decl =
      {
        Callable.call_decl_kind = Func;
        call_decl_name = Rewriter.ProgUtils.heap_utils_comp_chunk_ident loc;
        call_decl_formals =
          [
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x1")
              type_tp_expr;
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x2")
              type_tp_expr;
          ];
        call_decl_returns =
          [
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret")
              type_tp_expr;
          ];
        call_decl_locals = [];
        call_decl_precond = [];
        call_decl_postcond = [];
        call_decl_is_free = true;
        call_decl_is_auto = false;
        call_decl_loc = loc;
        call_decl_mask = Some (Set.empty (module QualIdent));
      }
    in

    let heap_add_chunk_fn =
      {
        Callable.call_decl = heap_add_chunk_fn_decl;
        call_def =
          FuncDef
            {
              func_body =
                Some
                  (Expr.mk_app ~loc ~typ:type_tp_expr
                     (Expr.Var
                        (Rewriter.ProgUtils.get_ra_comp_fn_qual_ident
                           ra_qual_ident))
                     [
                       Expr.from_var_decl
                         (List.hd_exn heap_add_chunk_fn_decl.call_decl_formals);
                       Expr.from_var_decl
                         (List.nth_exn heap_add_chunk_fn_decl.call_decl_formals
                            1);
                     ]);
            };
      }
    in

    let heap_sub_chunk_fn_decl =
      {
        Callable.call_decl_kind = Func;
        call_decl_name = Rewriter.ProgUtils.heap_utils_frame_chunk_ident loc;
        call_decl_formals =
          [
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x1")
              type_tp_expr;
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x2")
              type_tp_expr;
          ];
        call_decl_returns =
          [
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret")
              type_tp_expr;
          ];
        call_decl_locals = [];
        call_decl_precond = [];
        call_decl_postcond = [];
        call_decl_is_free = true;
        call_decl_is_auto = false;
        call_decl_mask = Some (Set.empty (module QualIdent));
        call_decl_loc = loc;
      }
    in

    let heap_sub_chunk_fn =
      {
        Callable.call_decl = heap_sub_chunk_fn_decl;
        call_def =
          FuncDef
            {
              func_body =
                Some
                  (Expr.mk_app ~loc ~typ:type_tp_expr
                     (Expr.Var
                        (Rewriter.ProgUtils.get_ra_frame_fn_qual_ident
                           ra_qual_ident))
                     [
                       Expr.from_var_decl
                         (List.hd_exn heap_sub_chunk_fn_decl.call_decl_formals);
                       Expr.from_var_decl
                         (List.nth_exn heap_sub_chunk_fn_decl.call_decl_formals
                            1);
                     ]);
            };
      }
    in

    let heapchunk_compare_fn_decl =
      {
        Callable.call_decl_kind = Func;
        call_decl_name =
          Rewriter.ProgUtils.heap_utils_heapchunk_compare_ident loc;
        call_decl_formals =
          [
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x1")
              type_tp_expr;
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x2")
              type_tp_expr;
          ];
        call_decl_returns =
          [
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret") Type.bool;
          ];
        call_decl_locals = [];
        call_decl_precond = [];
        call_decl_postcond = [];
        call_decl_is_free = true;
        call_decl_is_auto = false;
        call_decl_mask = Some (Set.empty (module QualIdent));
        call_decl_loc = loc;
      }
    in

    let heapchunk_compare_fn =
      {
        Callable.call_decl = heapchunk_compare_fn_decl;
        call_def =
          FuncDef
            {
              func_body =
                Some
                  (Expr.mk_app ~loc ~typ:type_tp_expr
                     (Expr.Var ra_valid_fn_qual_ident)
                     [
                       Expr.mk_app ~loc ~typ:type_tp_expr
                         (Expr.Var
                            (QualIdent.from_ident
                               heap_sub_chunk_fn_decl.call_decl_name))
                         [
                           Expr.from_var_decl
                             (List.hd_exn
                                heapchunk_compare_fn_decl.call_decl_formals);
                           Expr.from_var_decl
                             (List.nth_exn
                                heapchunk_compare_fn_decl.call_decl_formals 1);
                         ];
                     ]);
            };
      }
    in

    Rewriter.return
      [
        Module.SymbolDef (Module.TypeDef type_def);
        SymbolDef (Module.VarDef var_def);
        SymbolDef (Module.CallDef heap_valid_fn);
        SymbolDef (Module.CallDef heap_add_chunk_fn);
        SymbolDef (Module.CallDef heap_sub_chunk_fn);
        SymbolDef (Module.CallDef heapchunk_compare_fn);
      ]
  in

  Rewriter.return (Module.ModDef { mod_decl; mod_def })

let rewrite_add_field_utils (symbol : Module.symbol) : Module.symbol Rewriter.t
    =
  let open Rewriter.Syntax in
  match symbol with
  | FieldDef f ->
      let* utils_module =
        let ra_qual_ident = Rewriter.ProgUtils.field_get_ra_qual_iden f in
        let mod_ident =
          Rewriter.ProgUtils.field_utils_module_ident f.field_loc f.field_name
        in
        generate_utils_module ~is_field:true mod_ident ra_qual_ident f.field_loc
      in

      let* _ =
        Rewriter.introduce_typecheck_symbol ~loc:f.field_loc
          ~f:Typing.process_symbol utils_module
      in

      Rewriter.return symbol
  | _ -> Rewriter.return symbol

let rewrite_add_pred_utils (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_decl.call_decl_kind with
  | Pred | Invariant ->
      let loc = c.call_decl.call_decl_loc in
      let pred_ret_type =
        Type.mk_prod c.call_decl.call_decl_loc
          (List.map c.call_decl.call_decl_returns ~f:(fun var_decl ->
               var_decl.var_type))
      in

      let* pred_ret_type_module =
        Rewriter.ProgUtils.intros_type_module ~loc:c.call_decl.call_decl_loc
          ~f:Typing.process_symbol pred_ret_type
      in

      let mod_inst_type, mod_inst_def_ra =
        match c.call_decl.call_decl_kind with
        | Pred ->
            ( Predefs.lib_cancellative_ra_mod_qual_ident,
              Predefs.lib_countAgreeRA_mod_qual_ident )
        | Invariant ->
            ( Predefs.lib_lattice_ra_mod_qual_ident,
              Predefs.lib_agree_mod_qual_ident )
        | _ -> Error.internal_error loc "Expected a predicate or invariant"
      in

      let instantiated_pred_heap_ra =
        Module.ModInst
          {
            mod_inst_name =
              Rewriter.ProgUtils.pred_to_ra_mod_ident ~loc
                c.call_decl.call_decl_name;
            mod_inst_type;
            mod_inst_def = Some (mod_inst_def_ra, [ pred_ret_type_module ]);
            mod_inst_is_interface = false;
            mod_inst_loc = loc;
          }
      in

      let* pred_heap_ra =
        Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.process_symbol
          instantiated_pred_heap_ra
      in

      Logs.debug (fun m ->
          m "Generated pred heap RA module: %a" Module.pr_symbol
            instantiated_pred_heap_ra);

      let in_arg_typ =
        Type.mk_prod c.call_decl.call_decl_loc
          (List.map c.call_decl.call_decl_formals ~f:(fun var_decl ->
               var_decl.var_type))
      in

      let* utils_module =
        generate_utils_module ~is_field:false
          (Rewriter.ProgUtils.pred_utils_module_ident loc
             c.call_decl.call_decl_name)
          pred_heap_ra ~in_arg_typ loc
      in

      let* _ =
        Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.process_symbol
          utils_module
      in

      Rewriter.return c
  | _ -> Rewriter.return c

let rewrite_add_atomics_utils (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_decl.call_decl_kind with
  | Proc ->
      if not (Callable.is_atomic c.call_decl) then Rewriter.return c
      else
        let loc = c.call_decl.call_decl_loc in

        let proc_concrete_args_typ =
          Type.mk_prod c.call_decl.call_decl_loc
            (List.filter_map c.call_decl.call_decl_formals ~f:(fun var_decl ->
                 if var_decl.var_implicit then None else Some var_decl.var_type))
        in

        let* proc_conrete_args_type_module =
          Rewriter.ProgUtils.intros_type_module ~loc:c.call_decl.call_decl_loc
            ~f:Typing.process_symbol proc_concrete_args_typ
        in

        let proc_ret_type =
          Type.mk_prod c.call_decl.call_decl_loc
            (List.map c.call_decl.call_decl_returns ~f:(fun var_decl ->
                 var_decl.var_type))
        in

        let* proc_ret_type_module =
          Rewriter.ProgUtils.intros_type_module ~loc:c.call_decl.call_decl_loc
            ~f:Typing.process_symbol proc_ret_type
        in

        let instantiated_au_proc_heap_ra =
          Module.ModInst
            {
              mod_inst_name =
                Rewriter.ProgUtils.au_to_ra_mod_ident ~loc
                  c.call_decl.call_decl_name;
              mod_inst_type = Predefs.lib_ra_mod_qual_ident;
              mod_inst_def =
                Some
                  ( Predefs.lib_atomic_token_ra_mod_qual_ident,
                    [ proc_conrete_args_type_module; proc_ret_type_module ] );
              mod_inst_is_interface = false;
              mod_inst_loc = loc;
            }
        in

        let* au_proc_heap_ra =
          Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.process_symbol
            instantiated_au_proc_heap_ra
        in

        Logs.debug (fun m ->
            m "Generated au heap RA module: %a" Module.pr_symbol
              instantiated_au_proc_heap_ra);

        let in_arg_typ = Type.atomic_token in

        let* utils_module =
          generate_utils_module ~is_field:false
            (Rewriter.ProgUtils.au_utils_module_ident loc
               c.call_decl.call_decl_name)
            au_proc_heap_ra ~in_arg_typ loc
        in

        let* _ =
          Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.process_symbol
            utils_module
        in

        Rewriter.return c
  | _ -> Rewriter.return c

let introduce_heaps_in_stmts ~loc ~fields_list ~preds_list ~au_preds_list body :
    Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  (* TODO: Introduce variables of right types for predHeaps *)
  let* field_heap_var_defs =
    Rewriter.List.map fields_list ~f:(fun field_name ->
        let* field_symbol = Rewriter.find_and_reify Loc.dummy field_name in

        let field_elem_type =
          match field_symbol with
          | FieldDef f -> (
              match f.field_type with
              | App (Fld, [ tp_expr ], _) -> tp_expr
              | _ -> Error.type_error f.field_loc "Expected field identifier.")
          | _ -> Error.error Loc.dummy "Expected a field_def"
        in

        (* Done so that Ident is aware of this name being used; prevents the same name from being generated again during SSA transform *)
        let _ = Ident.fresh loc (field_heap_name field_name).ident_name in

        let (heap_var_decl : var_decl) =
          {
            var_name = field_heap_name field_name;
            var_loc = loc;
            var_type = Type.mk_map loc Type.ref field_elem_type;
            var_const = false;
            var_ghost = true;
            var_implicit = false;
          }
        in

        let loc = Stmt.to_loc body in
        let* field_utils_id =
          Rewriter.ProgUtils.get_field_utils_id loc field_name
        in

        let assume_expr1 =
          let l_var =
            Type.
              {
                var_name = Ident.fresh loc "l";
                var_loc = loc;
                var_type = Type.ref;
                var_const = false;
                var_ghost = false;
                var_implicit = false;
              }
          in

          let l_expr =
            Expr.mk_var ~typ:l_var.var_type
              (QualIdent.from_ident l_var.var_name)
          in

          Expr.mk_binder Forall [ l_var ]
            (Expr.mk_eq
               (Expr.mk_maplookup (Expr.from_var_decl heap_var_decl) l_expr)
               field_utils_id)
        in

        let _ = Ident.fresh loc (field_heap_name2 field_name).ident_name in

        let (heap_var_decl2 : var_decl) =
          {
            var_name = field_heap_name2 field_name;
            var_loc = loc;
            var_type = Type.mk_map loc Type.ref field_elem_type;
            var_const = false;
            var_ghost = true;
            var_implicit = false;
          }
        in

        let assume_expr2 =
          let l_var =
            {
              Type.var_name = Ident.fresh loc "l";
              var_loc = loc;
              var_type = Type.ref;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
          in

          let l_expr =
            Expr.mk_var ~typ:l_var.var_type
              (QualIdent.from_ident l_var.var_name)
          in

          Expr.mk_binder Forall [ l_var ]
            (Expr.mk_eq
               (Expr.mk_maplookup (Expr.from_var_decl heap_var_decl2) l_expr)
               field_utils_id)
        in

        Rewriter.return
          ( { Stmt.var_decl = heap_var_decl; var_init = None },
            { Stmt.var_decl = heap_var_decl2; var_init = None },
            Stmt.mk_assume_expr ~loc assume_expr1,
            Stmt.mk_assume_expr ~loc assume_expr2 ))
  in

  let* pred_heap_var_defs =
    Rewriter.List.map preds_list ~f:(fun pred_name ->
        let* pred_heap_elem_type_qual_ident =
          Rewriter.ProgUtils.get_pred_utils_rep_type loc pred_name
        in

        let pred_heap_elem_type =
          Type.mk_var loc pred_heap_elem_type_qual_ident
        in

        let* pred_in_types = Rewriter.ProgUtils.pred_in_types pred_name in

        (* Done so that Ident is aware of this name being used; prevents the same name from being generated again during SSA transform *)
        let _ = Ident.fresh loc (pred_heap_name pred_name).ident_name in

        let (heap_var_decl : var_decl) =
          {
            var_name = pred_heap_name pred_name;
            var_loc = loc;
            var_type =
              Type.mk_map loc
                (Type.mk_prod loc pred_in_types)
                pred_heap_elem_type;
            var_const = false;
            var_ghost = true;
            var_implicit = false;
          }
        in

        let loc = Stmt.to_loc body in
        let* pred_utils_id =
          Rewriter.ProgUtils.get_pred_utils_id loc pred_name
        in

        let assume_expr1 =
          let in_var =
            {
              Type.var_name = Ident.fresh loc "in";
              var_loc = loc;
              var_type = Type.mk_prod loc pred_in_types;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
          in

          let in_var_expr =
            Expr.mk_var ~typ:in_var.var_type
              (QualIdent.from_ident in_var.var_name)
          in

          Expr.mk_binder Forall [ in_var ]
            (Expr.mk_eq
               (Expr.mk_maplookup
                  (Expr.from_var_decl heap_var_decl)
                  in_var_expr)
               pred_utils_id)
        in

        let _ = Ident.fresh loc (pred_heap_name2 pred_name).ident_name in

        let (heap_var_decl2 : var_decl) =
          {
            var_name = pred_heap_name2 pred_name;
            var_loc = loc;
            var_type =
              Type.mk_map loc
                (Type.mk_prod loc pred_in_types)
                pred_heap_elem_type;
            var_const = false;
            var_ghost = true;
            var_implicit = false;
          }
        in

        let loc = Stmt.to_loc body in
        let assume_expr2 =
          let in_var =
            {
              Type.var_name = Ident.fresh loc "in";
              var_loc = loc;
              var_type = Type.mk_prod loc pred_in_types;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
          in

          let in_var_expr =
            Expr.mk_var ~typ:in_var.var_type
              (QualIdent.from_ident in_var.var_name)
          in

          Expr.mk_binder Forall [ in_var ]
            (Expr.mk_eq
               (Expr.mk_maplookup
                  (Expr.from_var_decl heap_var_decl2)
                  in_var_expr)
               pred_utils_id)
        in

        Rewriter.return
          ( { Stmt.var_decl = heap_var_decl; var_init = None },
            { Stmt.var_decl = heap_var_decl2; var_init = None },
            Stmt.mk_assume_expr ~loc assume_expr1,
            Stmt.mk_assume_expr ~loc assume_expr2 ))
  in

  let* au_heap_var_defs =
    Rewriter.List.map au_preds_list ~f:(fun call_name ->
        let* au_heap_elem_type_qual_ident =
          Rewriter.ProgUtils.get_au_utils_rep_type loc call_name
        in

        let au_heap_elem_type = Type.mk_var loc au_heap_elem_type_qual_ident in

        (* Done so that Ident is aware of this name being used; prevents the same name from being generated again during SSA transform *)
        let _ = Ident.fresh loc (au_heap_name call_name).ident_name in

        let (heap_var_decl : var_decl) =
          {
            var_name = au_heap_name call_name;
            var_loc = loc;
            var_type = Type.mk_map loc Type.atomic_token au_heap_elem_type;
            var_const = false;
            var_ghost = true;
            var_implicit = false;
          }
        in

        let* au_utils_id = Rewriter.ProgUtils.get_au_utils_id loc call_name in

        let assume_expr1 =
          let in_var =
            {
              Type.var_name = Ident.fresh loc "tok";
              var_loc = loc;
              var_type = Type.atomic_token;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
          in

          let in_var_expr =
            Expr.mk_var ~typ:in_var.var_type
              (QualIdent.from_ident in_var.var_name)
          in

          Expr.mk_binder Forall [ in_var ]
            (Expr.mk_eq
               (Expr.mk_maplookup
                  (Expr.from_var_decl heap_var_decl)
                  in_var_expr)
               au_utils_id)
        in

        let _ = Ident.fresh loc (au_heap_name2 call_name).ident_name in

        let (heap_var_decl2 : var_decl) =
          {
            var_name = au_heap_name2 call_name;
            var_loc = loc;
            var_type = Type.mk_map loc Type.atomic_token au_heap_elem_type;
            var_const = false;
            var_ghost = true;
            var_implicit = false;
          }
        in

        let assume_expr2 =
          let in_var =
            {
              Type.var_name = Ident.fresh loc "in";
              var_loc = loc;
              var_type = Type.atomic_token;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
          in

          let in_var_expr =
            Expr.mk_var ~typ:in_var.var_type
              (QualIdent.from_ident in_var.var_name)
          in

          Expr.mk_binder Forall [ in_var ]
            (Expr.mk_eq
               (Expr.mk_maplookup
                  (Expr.from_var_decl heap_var_decl2)
                  in_var_expr)
               au_utils_id)
        in

        Rewriter.return
          ( { Stmt.var_decl = heap_var_decl; var_init = None },
            { Stmt.var_decl = heap_var_decl2; var_init = None },
            Stmt.mk_assume_expr ~loc assume_expr1,
            Stmt.mk_assume_expr ~loc assume_expr2 ))
  in

  let* init_assumes =
    Rewriter.List.fold_left ~init:[]
      (field_heap_var_defs @ pred_heap_var_defs @ au_heap_var_defs)
      ~f:(fun
          assumes (heap_var_decl, heap_var_decl2, assume_stmt1, assume_stmt2) ->
        Logs.debug (fun m ->
            m
              "Rewrites.HeapsExplicitTrnsl.introduce_heaps_in_stmts: \
               heap_var_decl: %a; heap_var_decl2: %a"
              Ident.pr heap_var_decl.var_decl.var_name Ident.pr
              heap_var_decl2.var_decl.var_name);
        let* _ = Rewriter.introduce_symbol (Module.VarDef heap_var_decl) in
        let+ _ = Rewriter.introduce_symbol (Module.VarDef heap_var_decl2) in
        assume_stmt1 :: assume_stmt2 :: assumes)
  in

  Rewriter.return (Stmt.mk_block_stmt ~loc (init_assumes @ [ body ]))

let rec rewrite_fpu (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Fpu fpu_desc) ->
      let loc = Stmt.to_loc stmt in
      let* field_symbol =
        let* symbol = Rewriter.find_and_reify loc fpu_desc.fpu_field in
        match symbol with
        | FieldDef f -> Rewriter.return f
        | _ -> Error.error stmt.stmt_loc "Expected a field_def"
      in

      let field_expr =
        Expr.mk_var ~loc:stmt.stmt_loc ~typ:field_symbol.field_type
          fpu_desc.fpu_field
      in

      let fpu_allowed_qual_iden =
        let field_ra = Rewriter.ProgUtils.field_get_ra_qual_iden field_symbol in
        Rewriter.ProgUtils.get_ra_fpu_allowed_qual_ident field_ra
      in

      let* old_val =
        match fpu_desc.fpu_old_val with
        | Some expr -> Rewriter.return expr
        | None ->
            let* field_heap_symbol =
              let* symbol =
                Rewriter.find_and_reify loc
                  (QualIdent.from_ident (field_heap_name fpu_desc.fpu_field))
              in
              match symbol with
              | VarDef v -> Rewriter.return v.var_decl
              | _ -> Error.error stmt.stmt_loc "Expected a var_def"
            in

            Rewriter.return
            @@ Expr.mk_maplookup ~loc:stmt.stmt_loc
                 (Expr.from_var_decl field_heap_symbol)
                 fpu_desc.fpu_ref
      in

      let assert_stmt =
        let error =
          ( Error.Verification,
            stmt.stmt_loc,
            "This update may not be frame-preserving" )
        in
        Stmt.mk_assert_expr ~loc:stmt.stmt_loc
          ~cmnt:("FPU stmt: " ^ Stmt.to_string stmt)
          ~spec_error:[ Stmt.mk_const_spec_error error ]
          (Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.bool
             (Expr.Var fpu_allowed_qual_iden)
             [ old_val; fpu_desc.fpu_new_val ])
      in

      let exhale_stmt =
        let error =
          ( Error.Verification,
            stmt.stmt_loc,
            "This update may not be frame-preserving" )
        in
        Stmt.mk_exhale_expr ~loc:stmt.stmt_loc
          ~cmnt:("FPU stmt: " ^ Stmt.to_string stmt)
          ~spec_error:[ Stmt.mk_const_spec_error error ]
          (Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.perm Expr.Own
             [ fpu_desc.fpu_ref; field_expr; old_val ])
      in

      let inhale_stmt =
        Stmt.mk_inhale_expr ~loc:stmt.stmt_loc
          ~cmnt:("FPU stmt: " ^ Stmt.to_string stmt)
          (Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.perm Expr.Own
             [ fpu_desc.fpu_ref; field_expr; fpu_desc.fpu_new_val ])
      in

      let new_stmt =
        Stmt.mk_block_stmt ~loc:stmt.stmt_loc
          [ assert_stmt; exhale_stmt; inhale_stmt ]
      in

      Rewriter.return new_stmt
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_fpu

let rec rewrite_binds (stmt : Stmt.t) : Stmt.t Rewriter.t =
  match stmt.stmt_desc with
  | Basic (Bind bind_desc) ->
      let exis_vars =
        List.map bind_desc.bind_lhs ~f:(fun e ->
            Type.mk_var_decl ~loc:stmt.stmt_loc
              (Ident.fresh stmt.stmt_loc "$bind")
              (Expr.to_type e))
      in

      let alpha_renaming_map =
        List.fold2_exn bind_desc.bind_lhs exis_vars
          ~init:(Map.empty (module QualIdent))
          ~f:(fun renam_map e1 e2 ->
            Map.add_exn renam_map ~key:(Expr.to_qual_ident e1)
              ~data:(Expr.from_var_decl e2))
      in

      let error =
        ( Error.Verification,
          stmt.stmt_loc,
          "The body of bind stmt could not be shown" )
      in
      let assert_stmt =
        Stmt.mk_assert_expr ~loc:stmt.stmt_loc
          ~cmnt:("Bind stmt: " ^ Stmt.to_string stmt)
          ~spec_error:[ Stmt.mk_const_spec_error error ]
          (Expr.mk_binder Exists ~loc:stmt.stmt_loc exis_vars
             (Expr.alpha_renaming bind_desc.bind_rhs alpha_renaming_map))
      in

      let assume_stmt =
        Stmt.mk_assume_expr ~loc:stmt.stmt_loc
          ~cmnt:("Bind stmt: " ^ Stmt.to_string stmt)
          bind_desc.bind_rhs
      in

      let new_stmt =
        Stmt.mk_block_stmt ~loc:stmt.stmt_loc [ assert_stmt; assume_stmt ]
      in
      Rewriter.return new_stmt
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_binds

type expr_match = { var_decl : var_decl; expr : expr option }

let match_up_expr (expr1 : expr) (expr2 : expr) (vars : var_decl list) :
    (var_decl * expr) ident_map option =
  (* expr1 is the expr with vars; expr2 is the one to be matched against. So expr1 is allowed to have more existentials than expr2. For first implementation, expr2 is not allowed to have any existentials for now *)

  (* Return value of None represents that the expressions did not match up *)

  (* Running example:
          expr1: forall a :: f(a) ==> exists b :: e(a, b)
          expr2: forall a1 :: f(a1) ==> e(a1, v)

          vars: [b]
  *)
  Logs.debug (fun m ->
      m "Rewrites.HeapsExplicitTrnsl.match_up_expr: expr1: %a; expr2: %a"
        Expr.pr expr1 Expr.pr expr2);

  let rec match_up_expr (expr1 : expr) (expr2 : expr)
      (var_map : expr_match ident_map) : expr_match ident_map option =
    (* if Type.((Expr.to_type expr1) <> (Expr.to_type expr2)) then
         (Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.match_up_expr: Type mismatch: %a; %a" Type.pr (Expr.to_type expr1) Type.pr (Expr.to_type expr2));
         None)
       else *)
    match (expr1, expr2) with
    | Binder (Compr, v_d1, _, e1, _), Binder (Compr, v_d2, _, e2, _)
    | Binder (Forall, v_d1, _, e1, _), Binder (Forall, v_d2, _, e2, _) ->
        if not (Int.equal (List.length v_d1) (List.length v_d2)) then None
        else
          let typ_check =
            List.for_all2_exn v_d1 v_d2 ~f:(fun vd1 vd2 ->
                Type.equal vd1.var_type vd2.var_type)
          in

          if not typ_check then None
          else
            let renaming_map =
              List.fold2_exn v_d1 v_d2
                ~init:(Map.empty (module QualIdent))
                ~f:(fun renam_map vd1 vd2 ->
                  Map.add_exn renam_map
                    ~key:(QualIdent.from_ident vd2.var_name)
                    ~data:(Expr.from_var_decl vd1))
            in

            (* renaming expr2 to use the same universal quants as expr1 *)
            let e2 = Expr.alpha_renaming e2 renaming_map in

            match_up_expr e1 e2 var_map
    | Binder (Exists, v_d1, _, e1, _), e2 ->
        let var_map =
          List.fold v_d1 ~init:var_map ~f:(fun var_map vd1 ->
              match Map.find var_map vd1.var_name with
              | Some _ -> var_map
              | None ->
                  Error.error (Expr.to_loc expr1)
                    "Unexpected existential quantifier in expr1; expected all \
                     existentials to be declared in var_map")
        in

        match_up_expr e1 e2 var_map
    | App (constr1, exprs1, _), App (constr2, exprs2, _) -> (
        match constr1 with
        | Var qual_ident
          when List.exists (Map.keys var_map) ~f:(fun iden ->
                   QualIdent.equal (QualIdent.from_ident iden) qual_ident) -> (
            let var_iden = QualIdent.to_ident qual_ident in

            let expr_match = Map.find_exn var_map var_iden in
            match expr_match.expr with
            | None ->
                let var_map =
                  Map.set var_map ~key:var_iden
                    ~data:{ expr_match with expr = Some expr2 }
                in

                Some var_map
            | Some e -> if Expr.alpha_equal e expr2 then Some var_map else None)
        | _ ->
            if Expr.equal_constr constr1 constr2 then
              if
                (* Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.match_up_expr: expr1: %a; expr2: %a" Expr.pr expr1 Expr.pr expr2); *)
                List.length exprs1 <> List.length exprs2
              then None
              else
                let var_map_optn =
                  List.fold2_exn exprs1 exprs2 ~init:(Some var_map)
                    ~f:(fun var_map_optn e1 e2 ->
                      Option.flat_map var_map_optn ~f:(fun var_map ->
                          match_up_expr e1 e2 var_map))
                in

                var_map_optn
            else
              (* Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.match_up_expr: Constructor mismatch: %a; %a" Expr.pr expr1 Expr.pr expr2); *)
              None)
    | _ -> None
  in

  let var_map_optn =
    match_up_expr expr1 expr2
      (Map.of_alist_exn
         (module Ident)
         (List.map vars ~f:(fun var_decl ->
              (var_decl.var_name, { var_decl; expr = None }))))
  in

  match var_map_optn with
  | Some var_map ->
      Some
        (Map.map var_map ~f:(fun { var_decl; expr } ->
             match expr with
             | Some e -> (var_decl, e)
             | None ->
                 Error.error (Expr.to_loc expr1)
                   "Expected all variables to be matched up"))
  | None -> None

module ParseAssertionLang = struct
  let rec parse_a ?cmnt ?spec_error ~loc
      ?(universal_quants : universal_quants = { univ_vars = []; triggers = [] })
      (conds : conditions) (expr : expr) ~parse_a0 : Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    let parse_a = parse_a ?cmnt ~loc ?spec_error ~parse_a0 in
    match expr with
    | App (Ite, [ c; e1; e2 ], expr_attr) ->
        let* stmt1 = parse_a ~universal_quants (c :: conds) e1 in

        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = parse_a ~universal_quants (not_c :: conds) e2 in

        Rewriter.return (Stmt.mk_block_stmt ~loc [ stmt1; stmt2 ])
    | App (Impl, [ c; e2 ], expr_attr) ->
        parse_a ~universal_quants (c :: conds) e2
    | App (And, e_list, expr_attr) ->
        let* stmts_list =
          Rewriter.List.map e_list ~f:(fun e ->
              parse_a ~universal_quants conds e)
        in

        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
    | Binder (Forall, var_decls, trgs, e, expr_attr) ->
        let universal_quants =
          let new_quants =
            List.map var_decls ~f:(fun var_decl ->
                (var_decl.var_name, var_decl))
          in
          {
            univ_vars = universal_quants.univ_vars @ new_quants;
            triggers =
              (match universal_quants.triggers with
              | [] -> trgs
              | _ ->
                  List.concat_map universal_quants.triggers ~f:(fun trigs ->
                      List.map trgs ~f:(fun trg -> trigs @ trg)));
          }
        in

        let* stmt = parse_a ~universal_quants conds e in

        Rewriter.return stmt
    | _ -> parse_a0 ?cmnt ?spec_error ~loc universal_quants conds expr
end

module TrnslInhale = struct
  let rec skolemize_inhale_expr (universal_quants : universal_quants)
      (subst : expr qual_ident_map) (expr : expr) : expr Rewriter.t =
    let open Rewriter.Syntax in
    (* The difference between 
        generate_skolem_function_inhale and generate_skolem_function
      is that the former utilizes maps, whereas the latter utilizes functions.
    *)
    let generate_skolem_function_inhale (universal_quants : universal_quants)
        (var_decl : var_decl) : expr Rewriter.t =
      let univ_quants_list = universal_quants.univ_vars in
      (* univ_quants_list computed here to keep the ordering on keys constant for the construction *)
      if List.is_empty univ_quants_list then
        let var_decl =
          {
            var_decl with
            var_name = Ident.fresh var_decl.var_loc var_decl.var_name.ident_name;
          }
        in
        let symbol = Module.VarDef { var_decl; var_init = None } in
        let* _ = Rewriter.introduce_symbol symbol in

        Rewriter.return
          (Expr.mk_var ~typ:var_decl.var_type
             (QualIdent.from_ident var_decl.var_name))
      else
        let map_dom_type =
          Type.mk_prod var_decl.var_loc
            (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d.var_type))
        in
        let var_type =
          Type.mk_map var_decl.var_loc map_dom_type var_decl.var_type
        in

        let var_decl =
          {
            var_decl with
            var_name =
              Ident.fresh var_decl.var_loc
                ("skolem_" ^ var_decl.var_name.ident_name);
            var_type;
          }
        in
        let symbol = Module.VarDef { var_decl; var_init = None } in
        let* _ = Rewriter.introduce_symbol symbol in

        let tuple_expr =
          Expr.mk_tuple
            (List.map univ_quants_list ~f:(fun (_, v_d) ->
                 Expr.mk_var ~typ:v_d.var_type
                   (QualIdent.from_ident v_d.var_name)))
        in

        Rewriter.return
          (Expr.mk_maplookup
             (Expr.mk_var ~typ:var_decl.var_type
                (QualIdent.from_ident var_decl.var_name))
             tuple_expr)
    in

    match expr with
    | Binder (Forall, var_decls, trgs, e, e_attr) ->
        let universal_quants =
          let new_quants =
            List.map var_decls ~f:(fun var_decl ->
                (var_decl.var_name, var_decl))
          in
          {
            universal_quants with
            univ_vars = universal_quants.univ_vars @ new_quants;
          }
        in

        let* e = skolemize_inhale_expr universal_quants subst e in

        Rewriter.return Expr.(Binder (Forall, var_decls, trgs, e, e_attr))
    | Binder (Exists, var_decls, trgs, e, e_attr) ->
        let* subst =
          Rewriter.List.fold_left var_decls ~init:subst ~f:(fun map var_decl ->
              let* (new_expr : expr) =
                generate_skolem_function_inhale universal_quants var_decl
              in
              Rewriter.return
                (Map.add_exn map
                   ~key:(QualIdent.from_ident var_decl.var_name)
                   ~data:new_expr))
        in

        let* e = skolemize_inhale_expr universal_quants subst e in

        Logs.debug (fun m ->
            m
              "Rewrites.HeapsExplicitTrnsl.TrnslInhale.skolemize_inhale_expr: \
               found existentials:  e: %a"
              Expr.pr e
        );
        Rewriter.return e
    | _ ->
        let* expr =
          Rewriter.Expr.descend expr
            ~f:(skolemize_inhale_expr universal_quants subst)
        in

        let expr = Expr.alpha_renaming expr subst in

        (* This will cause the renaming to be done at each step of descend, but renaming should be idempotent, so that should be okay *)
        Logs.debug (fun m ->
            m
              "Rewrites.HeapsExplicitTrnsl.TrnslInhale.skolemize_inhale_expr: \
               e: %a"
              Expr.pr expr);
        Rewriter.return expr

  let rec rewriter_skolemize_inhale_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    match stmt.stmt_desc with
    | Basic (Spec (spec_kind, spec)) -> (
        match spec_kind with
        | Inhale ->
            let* e =
              skolemize_inhale_expr
                { univ_vars = []; triggers = [] }
                (Map.empty (module QualIdent))
                spec.spec_form
            in

            let spec = { spec with spec_form = e } in

            Rewriter.return
              { stmt with stmt_desc = Basic (Spec (spec_kind, spec)) }
        | _ -> Rewriter.return stmt)
    | _ -> Rewriter.Stmt.descend stmt ~f:rewriter_skolemize_inhale_stmts

  let rec rewriter_eliminate_binds_for_inhale (stmt : Stmt.t) :
      (Stmt.t, expr option) Rewriter.t_ext =
    let open Rewriter.Syntax in
    match stmt.stmt_desc with
    | Basic (Spec (Inhale, spec)) ->
        let* () = Rewriter.set_user_state (Some spec.spec_form) in
        Rewriter.return stmt
    | Basic (Spec (Assert, spec)) ->
        let* () = Rewriter.set_user_state (Some spec.spec_form) in
        Rewriter.return stmt
    | Basic (Bind bind_desc) -> (
        let* prev_expr = Rewriter.current_user_state in
        let* () = Rewriter.set_user_state None in

        match prev_expr with
        | None -> Rewriter.return stmt
        | Some prev_expr -> (
            Logs.debug (fun m ->
                m
                  "Rewrites.HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale: \
                   bind_desc: %a; prev_expr: %a"
                  Stmt.pr stmt Expr.pr prev_expr);

            let* bind_lhs_var_decls =
              Rewriter.List.map bind_desc.bind_lhs ~f:(fun var ->
                  let* symbol =
                    Rewriter.find_and_reify
                      (Expr.to_loc bind_desc.bind_rhs)
                      (Expr.to_qual_ident var)
                  in
                  match symbol with
                  | VarDef v -> Rewriter.return v.var_decl
                  | _ ->
                      Error.error
                        (Expr.to_loc bind_desc.bind_rhs)
                        "Expected a variable declaration")
            in

            match
              match_up_expr bind_desc.bind_rhs prev_expr bind_lhs_var_decls
            with
            | None ->
                Logs.debug (fun m ->
                    m
                      "Rewrites.HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale: \
                       Could not match up expressions");
                Rewriter.return stmt
            | Some var_map ->
                Logs.debug (fun m ->
                    m
                      "Rewrites.HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale: \
                       var_map: %a"
                      (Util.Print.pr_map ~key:Ident.pr ~value:Type.pr_var_decl)
                      (Map.map ~f:Stdlib.fst var_map));
                let assign_stmts =
                  List.map bind_lhs_var_decls ~f:(fun var_decl ->
                      let _, rhs = Map.find_exn var_map var_decl.var_name in

                      Stmt.mk_assign
                        ~loc:(Expr.to_loc bind_desc.bind_rhs)
                        [ Expr.from_var_decl var_decl ]
                        rhs)
                in

                Rewriter.return
                  (Stmt.mk_block_stmt
                     ~loc:(Expr.to_loc bind_desc.bind_rhs)
                     assign_stmts)))
    | _ ->
        let* () = Rewriter.set_user_state None in
        Rewriter.Stmt.descend stmt ~f:rewriter_eliminate_binds_for_inhale

  let rec trnsl_inhale_expr ?cmnt ?spec_error ~loc (expr : expr) :
      Stmt.t Rewriter.t =
    ParseAssertionLang.parse_a ?cmnt ?spec_error ~loc [] expr
      ~parse_a0:trnsl_inhale_a0

  and trnsl_inhale_a0 ?cmnt ?spec_error ~loc
      (universal_quants : universal_quants) (conds : conditions) (expr : expr) :
      Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    let univ_quants_list = universal_quants.univ_vars in
    let univ_vars_list =
      List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl)
    in

    match expr with
    | App (Own, [ e1; e2; e3 ], _) ->
        (* forall a, b, c :: m1(a, b, c) ==> own(f1(a, b, c), field, f2(a, b, c))

           ===>

           // asserting injectivity of functions
           assert forall a, b, c, a', b', c' :: m1(a, b, c) && m1(a', b', c') ==> f1(a, b, c) == f1(a', b', c') ==> (a == a' && b == b' && c == c')

           havoc(field$Heap2);

           assert forall l: Ref ::
             m1(inv(l)#0, inv(l)#1, inv(l)#2) && l == f1(inv(l)#0, inv(l)#1, inv(l)#2) ?
               field$Heap2[l] == field.comp( field$Heap[l], f2(inv(l)#0, inv(l)#1, inv(l)#2) ) :
             field$Heap2[l] == field$Heap[l]

           field$Heap := field$Heap2
           assume field.valid(field$Heap)
        *)
        let field_type =
          match Expr.to_type e2 with
          | App (Fld, [ tp_expr ], _) -> tp_expr
          | _ -> Error.type_error (Expr.to_loc e2) "Expected field identifier."
        in

        let field_name = Expr.to_qual_ident e2 in
        let field_heap_name = field_heap_name field_name in
        let field_heap_qual_ident = QualIdent.from_ident field_heap_name in
        let field_heap_expr =
          Expr.mk_var
            ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type)
            field_heap_qual_ident
        in

        let field_heap2_name = field_heap_name2 field_name in
        let field_heap2_qual_ident = QualIdent.from_ident field_heap2_name in
        let field_heap2_expr =
          Expr.mk_var
            ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type)
            field_heap2_qual_ident
        in

        let* (field_heapchunk_operator : qual_ident) =
          Rewriter.ProgUtils.get_field_utils_comp (Expr.to_loc e2) field_name
        in

        let* (field_heap_valid_fn : qual_ident) =
          Rewriter.ProgUtils.get_field_utils_valid (Expr.to_loc e2) field_name
        in

        let l_var =
          Type.
            {
              var_name = Ident.fresh (Expr.to_loc expr) "l";
              var_loc = Expr.to_loc expr;
              var_type = Type.ref;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
        in

        let l_expr =
          Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name)
        in

        let* inv_fn_expr =
          generate_inv_function ~loc universal_quants conds e1 ~arg_expr:l_expr
        in

        let inv_exprs =
          List.mapi univ_vars_list ~f:(fun index _var_decl ->
              Expr.mk_tuple_lookup inv_fn_expr index)
        in

        
        (* inhale forall i, j :: { v(i,j) } own(f(i, j), fld, v(i, j))
          *   ~~>
          * forall i, j :: { v(i,j) } 
          *  v[
          *      i <- inv(f(i, j), i, j)#0, 
          *      j <- inv(f(i, j), i, j)#1
          *  ] (var substitution)
          *    = 
          *  v(i, j) *)
        let* forward_trigger_assertion =
          let inv_fn_qi = (match inv_fn_expr with
            | App ((Expr.Var inv_fn_qi), args, _) -> inv_fn_qi
            | _ -> 
              Error.internal_error loc "Expected inv function call (i/own)"            
          ) in

          let+ env_local_var_decls =
            compute_env_local_var_decls ~loc e1 conds universal_quants
          in
          
          let inv_expr = 
            Expr.mk_app ~loc 
              ~typ:(Type.mk_prod loc 
                (List.map univ_vars_list ~f:(fun var_decl -> var_decl.var_type))
              )  
              (Expr.Var inv_fn_qi) 
                (e1 :: (List.map env_local_var_decls ~f:Expr.from_var_decl))
          in 

          (* i ~> inv(f(i, j), i, j)#0
           * j ~> inv(f(i, j), i, j)#1*)
          let renaming_map =
            List.foldi univ_vars_list 
              ~init:(Map.empty (module QualIdent))
              ~f:(fun index map var_decl ->
                Map.set map
                  ~key:(QualIdent.from_ident var_decl.var_name)
                  ~data:(Expr.mk_tuple_lookup ~loc inv_expr index))
          in
          let expr = Expr.alpha_renaming e3 renaming_map 
          
          in

          Stmt.mk_assume_expr ~loc  ~cmnt:"forward_trigger_assertion" (
            Expr.mk_binder ~trigs:universal_quants.triggers ~loc ~typ:Type.bool Forall univ_vars_list
            (Expr.mk_eq ~loc expr e3)
          )
        in

        let alpha_renaming_map =
          List.fold2_exn univ_vars_list inv_exprs
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl expr ->
              Map.set map
                ~key:(QualIdent.from_ident var_decl.var_name)
                ~data:expr)
        in

        let e1_subst = Expr.alpha_renaming e1 alpha_renaming_map in
        let e3_subst = Expr.alpha_renaming e3 alpha_renaming_map in
        let conds_subst =
          List.map conds ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in

        let havoc_stmt = Stmt.mk_havoc ~loc field_heap2_qual_ident in
        let assume_stmt =
          let l_eq_e1_expr = Expr.mk_eq l_expr e1_subst in

          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt ^ "\n")
              ^ "inhale: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                    (Expr.mk_impl (Expr.mk_and conds) expr)))
            (Expr.mk_binder
               ~trigs:
                 [
                   [ Expr.mk_maplookup ~loc field_heap2_expr l_expr ];
                   [ Expr.mk_maplookup ~loc field_heap_expr l_expr ];
                 ]
               ~loc ~typ:Type.bool Forall [ l_var ]
               (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                  [
                    (* m1(a,b,c) && l == f1(a, b, c) *)
                    Expr.mk_and ~loc (l_eq_e1_expr :: conds_subst);
                    (* field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                    Expr.mk_eq ~loc
                      (Expr.mk_maplookup ~loc field_heap2_expr e1_subst)
                      (Expr.mk_app ~loc ~typ:field_type
                         (Expr.Var field_heapchunk_operator)
                         [
                           Expr.mk_maplookup ~loc field_heap_expr l_expr;
                           e3_subst;
                         ]);
                    (* field$Heap2[l] == field$Heap[l] *)
                    Expr.mk_eq ~loc
                      (Expr.mk_maplookup ~loc field_heap2_expr l_expr)
                      (Expr.mk_maplookup ~loc field_heap_expr l_expr);
                  ]))
        in

        (* field$Heap := field$Heap2 *)
        let eq_stmt =
          Stmt.mk_assign ~loc [ field_heap_expr ] field_heap2_expr
        in

        let assume_heap_valid =
          Stmt.mk_assume_expr ~loc
            (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var field_heap_valid_fn)
               [ field_heap_expr ])
        in

        let* injectivity_assertion =
          generate_injectivity_assertions ~loc universal_quants conds e1
        in

        let stmts_list =
          match univ_quants_list with
          | [] -> []
          | _ -> [ injectivity_assertion ]
        in

        let stmts_list =
          stmts_list @ [ havoc_stmt; assume_stmt; forward_trigger_assertion; eq_stmt; assume_heap_valid ]
        in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt
    | App (AUPred call_qual_ident, token :: args, _)
    | App (AUPredCommit call_qual_ident, token :: args, _) ->
        Logs.debug (fun m ->
            m
              "Rewrites.HeapsExplicitTrnsl.TrnslInhale.trnsl_inhale_a0: expr: \
               %a"
              Expr.pr expr);
        let loc = Expr.to_loc expr in
        let* heap_elem_type_qual_iden =
          Rewriter.ProgUtils.get_au_utils_rep_type loc call_qual_ident
        in

        let heap_elem_type = Type.mk_var loc heap_elem_type_qual_iden in

        let call_name = call_qual_ident in
        let au_heap_name = au_heap_name call_name in
        let au_heap_qual_ident = QualIdent.from_ident au_heap_name in
        let au_heap_expr =
          Expr.mk_var
            ~typ:(Type.mk_map loc Type.ref heap_elem_type)
            au_heap_qual_ident
        in

        let au_heap2_name = au_heap_name2 call_name in
        let au_heap2_qual_ident = QualIdent.from_ident au_heap2_name in
        let au_heap2_expr =
          Expr.mk_var
            ~typ:(Type.mk_map loc Type.ref heap_elem_type)
            au_heap2_qual_ident
        in

        let* (au_heapchunk_operator : qual_ident) =
          Rewriter.ProgUtils.get_au_utils_comp loc call_name
        in

        let* (au_heap_valid_fn : qual_ident) =
          Rewriter.ProgUtils.get_au_utils_valid loc call_name
        in

        let* au_ra_uncommitted_constr =
          Rewriter.ProgUtils.au_ra_uncommitted_constr_qual_ident loc
            call_qual_ident
        in
        let* au_ra_committed_constr =
          Rewriter.ProgUtils.au_ra_committed_constr_qual_ident loc
            call_qual_ident
        in

        let havoc_stmt = Stmt.mk_havoc ~loc au_heap2_qual_ident in

        let new_token_var =
          {
            Type.var_name = Ident.fresh loc "tok";
            var_loc = loc;
            var_type = Type.atomic_token;
            var_const = false;
            var_ghost = false;
            var_implicit = false;
          }
        in

        let new_token_expr = Expr.from_var_decl new_token_var in

        let* inv_fn_expr =
          generate_inv_function ~loc universal_quants conds token
            ~arg_expr:new_token_expr
        in

        let inv_exprs =
          List.mapi univ_vars_list ~f:(fun index var_decl ->
              Expr.mk_tuple_lookup inv_fn_expr index)
        in

        (* inhale forall i, j :: { v(i,j) } AUPred(proc, gamma(i,j), (a_1, ... a_k)(i, j))
        *   ~~>
        * forall i, j :: { v(i,j) } 
        *  (a_1, ... a_k)[
        *      i <- inv(f(i, j), i, j)#0, 
        *      j <- inv(f(i, j), i, j)#1
        *  ] (var substitution)
        *    = 
        *  (a_1, ... a_k)(i, j) *)
        let* forward_trigger_assertion =
          let inv_fn_qi = (match inv_fn_expr with
            | App ((Expr.Var inv_fn_qi), args, _) -> inv_fn_qi
            | _ -> 
              Error.internal_error loc "Expected inv function call (i/au)"            
          ) in

          let+ env_local_var_decls =
            compute_env_local_var_decls ~loc token conds universal_quants
          in
          
          let inv_expr = 
            Expr.mk_app ~loc 
              ~typ:(Type.mk_prod loc 
                (List.map univ_vars_list ~f:(fun var_decl -> var_decl.var_type))
              )  
              (Expr.Var inv_fn_qi) 
                (token :: (List.map env_local_var_decls ~f:Expr.from_var_decl))
          in 

          (* i ~> inv(f(i, j), i, j)#0
            * j ~> inv(f(i, j), i, j)#1*)
          let renaming_map =
            List.foldi univ_vars_list 
              ~init:(Map.empty (module QualIdent))
              ~f:(fun index map var_decl ->
                Map.set map
                  ~key:(QualIdent.from_ident var_decl.var_name)
                  ~data:(Expr.mk_tuple_lookup ~loc inv_expr index))
          in
          let expr = Expr.alpha_renaming (Expr.mk_tuple args) renaming_map 
          
          in

          Stmt.mk_assume_expr ~loc  ~cmnt:"forward_trigger_assertion" (
            Expr.mk_binder ~trigs:universal_quants.triggers ~loc ~typ:Type.bool Forall univ_vars_list
            (Expr.mk_eq ~loc expr (Expr.mk_tuple args))
          )
        in

        let alpha_renaming_map =
          List.fold2_exn univ_vars_list inv_exprs
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl expr ->
              Map.set map
                ~key:(QualIdent.from_ident var_decl.var_name)
                ~data:expr)
        in

        let token_subst = Expr.alpha_renaming token alpha_renaming_map in
        let args_subst =
          List.map args ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in
        let conds_subst =
          List.map conds ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in

        let assume_stmt =
          let token_var_eq_given_token =
            Expr.mk_eq new_token_expr token_subst
          in

          let new_chunk =
            match expr with
            | App (AUPred _, _, _) ->
                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_uncommitted_constr)
                  [ Expr.mk_tuple args_subst ]
            | App (AUPredCommit _, _, _) ->
                let ret_val = List.last_exn args_subst in
                let call_args = List.drop_last_exn args_subst in

                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_committed_constr)
                  [ Expr.mk_tuple call_args; ret_val ]
            | _ -> Error.error loc "Internal error"
          in

          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt)
              ^ "\ninhale: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                    (Expr.mk_impl (Expr.mk_and conds) expr)))
            (Expr.mk_binder
               ~trigs:
                 [
                   [ Expr.mk_maplookup ~loc au_heap2_expr new_token_expr ];
                   [ Expr.mk_maplookup ~loc au_heap_expr new_token_expr ];
                 ]
               ~loc ~typ:Type.bool Forall [ new_token_var ]
               (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                  [
                    (* m1(a,b,c) && l == f1(a, b, c) *)
                    Expr.mk_and ~loc (token_var_eq_given_token :: conds_subst);
                    (* au$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                    Expr.mk_eq ~loc
                      (Expr.mk_maplookup ~loc au_heap2_expr token_subst)
                      (Expr.mk_app ~loc ~typ:heap_elem_type
                         (Expr.Var au_heapchunk_operator)
                         [
                           Expr.mk_maplookup ~loc au_heap_expr new_token_expr;
                           new_chunk;
                         ]);
                    (* au$Heap2[l] == au$Heap[l] *)
                    Expr.mk_eq ~loc
                      (Expr.mk_maplookup ~loc au_heap2_expr new_token_expr)
                      (Expr.mk_maplookup ~loc au_heap_expr new_token_expr);
                  ]))
        in

        (* au$Heap := au$Heap2 *)
        let eq_stmt = Stmt.mk_assign ~loc [ au_heap_expr ] au_heap2_expr in

        let assume_heap_valid =
          Stmt.mk_assume_expr ~loc
            (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var au_heap_valid_fn)
               [ au_heap_expr ])
        in

        let* injectivity_assertion =
          generate_injectivity_assertions ~loc universal_quants conds token
        in

        let stmts_list =
          match univ_quants_list with
          | [] -> []
          | _ -> [ injectivity_assertion ]
        in

        let stmts_list =
          stmts_list @ [ havoc_stmt; assume_stmt; forward_trigger_assertion; eq_stmt; assume_heap_valid ]
        in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt
    | e -> (
        let* is_e_pure = Rewriter.ProgUtils.is_expr_pure e in
        if is_e_pure then
          let body_expr =
            match conds with [] -> e | _ -> Expr.mk_impl (Expr.mk_and conds) e
          in
          let assume_expr =
            Expr.mk_binder ~loc ~typ:Type.bool ~trigs:universal_quants.triggers
              Forall
              (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d))
              body_expr
          in
          Rewriter.return
            (Stmt.mk_assume_expr ~loc
               ~cmnt:
                  ((match cmnt with None -> "" | Some cmnt -> cmnt)
                  ^ "\ninhale: "
                  ^ Stdlib.Format.asprintf "%a" Expr.pr
                      (Expr.mk_binder Forall univ_vars_list
                          (Expr.mk_impl (Expr.mk_and conds) expr)))
               assume_expr)
        else
          match e with
          | App (Var qual_ident, args, _) -> (
              let* symbol = Rewriter.find_and_reify loc qual_ident in
              match symbol with
              | CallDef c
                when Poly.(
                       c.call_decl.call_decl_kind = Pred
                       || c.call_decl.call_decl_kind = Invariant) ->
                  let* heap_elem_type_qual_iden =
                    Rewriter.ProgUtils.get_pred_utils_rep_type loc qual_ident
                  in

                  let heap_elem_type =
                    Type.mk_var loc heap_elem_type_qual_iden
                  in

                  let pred_name = qual_ident in
                  let pred_heap_name = pred_heap_name pred_name in
                  let pred_heap_qual_ident =
                    QualIdent.from_ident pred_heap_name
                  in
                  let pred_heap_expr =
                    Expr.mk_var
                      ~typ:(Type.mk_map loc Type.ref heap_elem_type)
                      pred_heap_qual_ident
                  in

                  let pred_heap2_name = pred_heap_name2 pred_name in
                  let pred_heap2_qual_ident =
                    QualIdent.from_ident pred_heap2_name
                  in
                  let pred_heap2_expr =
                    Expr.mk_var
                      ~typ:(Type.mk_map loc Type.ref heap_elem_type)
                      pred_heap2_qual_ident
                  in

                  let* (pred_heapchunk_operator : qual_ident) =
                    Rewriter.ProgUtils.get_pred_utils_comp loc pred_name
                  in

                  let* (pred_heap_valid_fn : qual_ident) =
                    Rewriter.ProgUtils.get_pred_utils_valid loc pred_name
                  in

                  let* pred_in_types =
                    Rewriter.ProgUtils.pred_in_types qual_ident
                  in

                  let* pred_out_types =
                    Rewriter.ProgUtils.pred_out_types qual_ident
                  in

                  let* pred_ra_constr =
                    Rewriter.ProgUtils.pred_ra_constr_qual_ident loc qual_ident
                  in

                  let in_vars =
                    List.map pred_in_types ~f:(fun tp ->
                        {
                          Type.var_name = Ident.fresh loc "in";
                          var_loc = Expr.to_loc e;
                          var_type = tp;
                          var_const = false;
                          var_ghost = false;
                          var_implicit = false;
                        })
                  in

                  let in_vars_exprs =
                    List.map in_vars ~f:(fun v -> Expr.from_var_decl v)
                  in
                  let in_vars_tuple = Expr.mk_tuple in_vars_exprs in

                  let actual_arg_in_exprs =
                    List.take args (List.length pred_in_types)
                  in
                  let actual_arg_out_exprs =
                    List.drop args (List.length pred_in_types)
                  in

                  let* inv_fn_expr =
                    generate_inv_function ~loc universal_quants conds
                      (Expr.mk_tuple actual_arg_in_exprs)
                      ~arg_expr:in_vars_tuple
                  in

                  let inv_exprs =
                    List.mapi univ_vars_list ~f:(fun index var_decl ->
                        Expr.mk_tuple_lookup inv_fn_expr index)
                  in

                  (* inhale forall i, j :: { v(i,j) } pred(ins(i, j); outs(i, j))
                  *   ~~>
                  * forall i, j :: { v(i,j) } 
                  *  outs[
                  *      i <- inv(f(i, j), i, j)#0, 
                  *      j <- inv(f(i, j), i, j)#1
                  *  ] (var substitution)
                  *    = 
                  *  outs(i, j) *)
                  let* forward_trigger_assertion =
                    let inv_fn_qi_opt = (match inv_fn_expr with
                      | App ((Expr.Var inv_fn_qi), args, _) -> 
                        Some inv_fn_qi
                      | _ -> 
                        None

                        (* Error.internal_error loc ("Expected inv function call  (i/pred)"*)
                    ) in
                    
                    begin match inv_fn_qi_opt with
                    | None -> 
                      Rewriter.return (Stmt.mk_skip ~loc)

                    | Some inv_fn_qi ->
                      let+ env_local_var_decls =
                        compute_env_local_var_decls ~loc (Expr.mk_tuple actual_arg_in_exprs) conds universal_quants
                      in
                      
                      let inv_expr = 
                        Expr.mk_app ~loc 
                          ~typ:(Type.mk_prod loc 
                            (List.map univ_vars_list ~f:(fun var_decl -> var_decl.var_type))
                          )  
                          (Expr.Var inv_fn_qi) 
                            ((Expr.mk_tuple actual_arg_in_exprs) :: (List.map env_local_var_decls ~f:Expr.from_var_decl))
                      in 
            
                      (* i ~> inv(f(i, j), i, j)#0
                      * j ~> inv(f(i, j), i, j)#1*)
                      let renaming_map =
                        List.foldi univ_vars_list 
                          ~init:(Map.empty (module QualIdent))
                          ~f:(fun index map var_decl ->
                            Map.set map
                              ~key:(QualIdent.from_ident var_decl.var_name)
                              ~data:(Expr.mk_tuple_lookup ~loc inv_expr index))
                      in
                      let expr = Expr.alpha_renaming (Expr.mk_tuple actual_arg_out_exprs) renaming_map 
                      
                      in
            
                      Stmt.mk_assume_expr ~loc  ~cmnt:"forward_trigger_assertion" (
                        Expr.mk_binder ~trigs:universal_quants.triggers ~loc ~typ:Type.bool Forall univ_vars_list
                        (Expr.mk_eq ~loc expr (Expr.mk_tuple actual_arg_out_exprs))
                      )
                    end
                  in

                  let alpha_renaming_map =
                    List.fold2_exn univ_vars_list inv_exprs
                      ~init:(Map.empty (module QualIdent))
                      ~f:(fun map var_decl expr ->
                        Map.set map
                          ~key:(QualIdent.from_ident var_decl.var_name)
                          ~data:expr)
                  in

                  let actual_arg_in_exprs_subst =
                    List.map actual_arg_in_exprs ~f:(fun e ->
                        Expr.alpha_renaming e alpha_renaming_map)
                  in
                  let actual_arg_in_exprs_subst_tuple =
                    Expr.mk_tuple actual_arg_in_exprs_subst
                  in
                  let actual_arg_out_exprs_subst =
                    List.map actual_arg_out_exprs ~f:(fun e ->
                        Expr.alpha_renaming e alpha_renaming_map)
                  in
                  let conds_subst =
                    List.map conds ~f:(fun e ->
                        Expr.alpha_renaming e alpha_renaming_map)
                  in

                  let havoc_stmt = Stmt.mk_havoc ~loc pred_heap2_qual_ident in

                  let assume_stmt =
                    let in_vars_eq_args =
                      Expr.mk_eq in_vars_tuple actual_arg_in_exprs_subst_tuple
                    in

                    let new_chunk =
                      let new_chunk_expr_list =
                        match c.call_decl.call_decl_kind with
                        | Pred ->
                            [
                              Expr.mk_int 1;
                              Expr.mk_tuple actual_arg_out_exprs_subst;
                            ]
                        | Invariant ->
                            [ Expr.mk_tuple actual_arg_out_exprs_subst ]
                        | _ ->
                            Error.error loc
                              "Internal error: Expected a predicate or \
                               invariant"
                      in

                      Expr.mk_app ~loc ~typ:heap_elem_type
                        (Expr.DataConstr pred_ra_constr) new_chunk_expr_list
                    in

                    Stmt.mk_assume_expr ~loc
                      ~cmnt:
                        ((match cmnt with None -> "" | Some cmnt -> cmnt)
                        ^ "\ninhale: "
                        ^ Stdlib.Format.asprintf "%a" Expr.pr
                            (Expr.mk_binder Forall univ_vars_list
                              (Expr.mk_impl (Expr.mk_and conds) expr)))
                      (Expr.mk_binder
                         ~trigs:
                           [
                             [
                               Expr.mk_maplookup ~loc pred_heap2_expr
                                 in_vars_tuple;
                             ];
                             [
                               Expr.mk_maplookup ~loc pred_heap_expr
                                 in_vars_tuple;
                             ];
                           ]
                         ~loc ~typ:Type.bool Forall in_vars
                         (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                            [
                              (* m1(a,b,c) && l == f1(a, b, c) *)
                              Expr.mk_and ~loc (in_vars_eq_args :: conds_subst);
                              (* pred$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                              Expr.mk_eq ~loc
                                (Expr.mk_maplookup ~loc pred_heap2_expr
                                   actual_arg_in_exprs_subst_tuple)
                                (Expr.mk_app ~loc ~typ:heap_elem_type
                                   (Expr.Var pred_heapchunk_operator)
                                   [
                                     Expr.mk_maplookup ~loc pred_heap_expr
                                       in_vars_tuple;
                                     new_chunk;
                                   ]);
                              (* pred$Heap2[l] == pred$Heap[l] *)
                              Expr.mk_eq ~loc
                                (Expr.mk_maplookup ~loc pred_heap2_expr
                                   in_vars_tuple)
                                (Expr.mk_maplookup ~loc pred_heap_expr
                                   in_vars_tuple);
                            ]))
                  in

                  (* pred$Heap := pred$Heap2 *)
                  let eq_stmt =
                    Stmt.mk_assign ~loc [ pred_heap_expr ] pred_heap2_expr
                  in

                  let assume_heap_valid =
                    Stmt.mk_assume_expr ~loc
                      (Expr.mk_app ~loc ~typ:Type.bool
                         (Expr.Var pred_heap_valid_fn) [ pred_heap_expr ])
                  in

                  let* injectivity_assertion =
                    generate_injectivity_assertions ~loc universal_quants conds
                      (Expr.mk_tuple actual_arg_in_exprs)
                  in

                  let stmts_list =
                    match univ_quants_list with
                    | [] -> []
                    | _ -> [ injectivity_assertion ]
                  in

                  let stmts_list =
                    stmts_list
                    @ [ havoc_stmt; assume_stmt; forward_trigger_assertion; eq_stmt; assume_heap_valid ]
                  in

                  let stmt = Stmt.mk_block_stmt ~loc stmts_list in

                  Rewriter.return stmt
              | _ -> Error.error loc "Expected a predicate definition")
          | _ -> unsupported_expr_error expr)

  let rec trnsl_assume_expr ?cmnt ?spec_error ~loc (expr : expr) :
      Stmt.t Rewriter.t =
    ParseAssertionLang.parse_a ?cmnt ?spec_error ~loc [] expr
      ~parse_a0:trnsl_assume_a0
  (* trnsl_assume_a ?cmnt ~loc [] expr *)

  and trnsl_assume_a0 ?cmnt ?spec_error ~loc
      (universal_quants : universal_quants) (conds : conditions) (expr : expr) :
      Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    let univ_quants_list = universal_quants.univ_vars in
    let univ_vars_list =
      List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl)
    in

    match expr with
    | App (Own, [ e1; e2; e3 ], _) ->
        (* forall a, b, c :: m1(a, b, c) ==> own(f1(a, b, c), field, f2(a, b, c))

           ===>

           assert forall a, b, c :: m1(a,b,c) ==>
                 heapChunkCompare ( field$Heap[l], f2(a, b, c) )
        *)
        let field_type =
          match Expr.to_type e2 with
          | App (Fld, [ tp_expr ], _) -> tp_expr
          | _ -> Error.type_error (Expr.to_loc e2) "Expected field identifier."
        in

        let field_name = Expr.to_qual_ident e2 in
        let field_heap_name = field_heap_name field_name in
        let field_heap_qual_ident = QualIdent.from_ident field_heap_name in
        let field_heap_expr =
          Expr.mk_var
            ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type)
            field_heap_qual_ident
        in

        let* (field_heapchunk_operator : qual_ident) =
          Rewriter.ProgUtils.get_field_utils_heapchunk_compare (Expr.to_loc e2)
            field_name
        in

        let* (field_heap_valid_fn : qual_ident) =
          Rewriter.ProgUtils.get_field_utils_valid (Expr.to_loc e2) field_name
        in

        let assume_stmt =
          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt ^ "\n")
              ^ "assume: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                    (Expr.mk_impl (Expr.mk_and conds) expr)))
            (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
               (Expr.mk_impl ~loc (Expr.mk_and ~loc conds)
                  (Expr.mk_app ~loc ~typ:Type.bool
                     (Expr.Var field_heapchunk_operator)
                     [ Expr.mk_maplookup ~loc field_heap_expr e1; e3 ])))
        in

        Rewriter.return assume_stmt
    | App (AUPred call_qual_ident, token :: args, _)
    | App (AUPredCommit call_qual_ident, token :: args, _) ->
        Logs.debug (fun m ->
            m
              "Rewrites.HeapsExplicitTrnsl.Trnslassume.trnsl_assume_a0: expr: \
               %a"
              Expr.pr expr);
        let loc = Expr.to_loc expr in
        let* heap_elem_type_qual_iden =
          Rewriter.ProgUtils.get_au_utils_rep_type loc call_qual_ident
        in

        let heap_elem_type = Type.mk_var loc heap_elem_type_qual_iden in

        let call_name = call_qual_ident in
        let au_heap_name = au_heap_name call_name in
        let au_heap_qual_ident = QualIdent.from_ident au_heap_name in
        let au_heap_expr =
          Expr.mk_var
            ~typ:(Type.mk_map loc Type.ref heap_elem_type)
            au_heap_qual_ident
        in

        let* (au_heapchunk_operator : qual_ident) =
          Rewriter.ProgUtils.get_au_utils_heapchunk_compare loc call_name
        in

        let* au_ra_uncommitted_constr =
          Rewriter.ProgUtils.au_ra_uncommitted_constr_qual_ident loc
            call_qual_ident
        in
        let* au_ra_committed_constr =
          Rewriter.ProgUtils.au_ra_committed_constr_qual_ident loc
            call_qual_ident
        in

        let assume_stmt =
          let new_chunk =
            match expr with
            | App (AUPred _, _ :: args, _) ->
                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_uncommitted_constr)
                  [ Expr.mk_tuple args ]
            | App (AUPredCommit _, _ :: args, _) ->
                let ret_val = List.last_exn args in
                let call_args = List.drop_last_exn args in

                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_committed_constr)
                  [ Expr.mk_tuple call_args; ret_val ]
            | _ -> Error.error loc "Internal error"
          in

          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt)
              ^ "\nassume: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                    (Expr.mk_impl (Expr.mk_and conds) expr)))
            (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
               (Expr.mk_impl ~loc (Expr.mk_and ~loc conds)
                  (Expr.mk_app ~loc ~typ:Type.bool
                     (Expr.Var au_heapchunk_operator)
                     [ Expr.mk_maplookup ~loc au_heap_expr token; new_chunk ])))
        in

        Rewriter.return assume_stmt
    | e -> (
        let* is_e_pure = Rewriter.ProgUtils.is_expr_pure e in
        if is_e_pure then
          let body_expr =
            match conds with [] -> e | _ -> Expr.mk_impl (Expr.mk_and conds) e
          in
          let assume_expr =
            Expr.mk_binder ~loc ~typ:Type.bool ~trigs:universal_quants.triggers
              Forall
              (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d))
              body_expr
          in
          Rewriter.return
            (Stmt.mk_assume_expr ~loc
               ~cmnt:
                  ((match cmnt with None -> "" | Some cmnt -> cmnt)
                  ^ "\nassume: "
                  ^ Stdlib.Format.asprintf "%a" Expr.pr
                      (Expr.mk_binder Forall univ_vars_list
                          (Expr.mk_impl (Expr.mk_and conds) expr)))
               assume_expr)
        else
          match e with
          | App (Var qual_ident, args, _) -> (
              let* symbol = Rewriter.find_and_reify loc qual_ident in
              match symbol with
              | CallDef c
                when Poly.(
                       c.call_decl.call_decl_kind = Pred
                       || c.call_decl.call_decl_kind = Invariant) ->
                  let* heap_elem_type_qual_iden =
                    Rewriter.ProgUtils.get_pred_utils_rep_type loc qual_ident
                  in

                  let heap_elem_type =
                    Type.mk_var loc heap_elem_type_qual_iden
                  in

                  let pred_name = qual_ident in
                  let pred_heap_name = pred_heap_name pred_name in
                  let pred_heap_qual_ident =
                    QualIdent.from_ident pred_heap_name
                  in
                  let pred_heap_expr =
                    Expr.mk_var
                      ~typ:(Type.mk_map loc Type.ref heap_elem_type)
                      pred_heap_qual_ident
                  in

                  let* (pred_heapchunk_operator : qual_ident) =
                    Rewriter.ProgUtils.get_pred_utils_heapchunk_compare loc
                      pred_name
                  in

                  let* pred_in_types =
                    Rewriter.ProgUtils.pred_in_types qual_ident
                  in

                  let* pred_out_types =
                    Rewriter.ProgUtils.pred_out_types qual_ident
                  in

                  let* pred_ra_constr =
                    Rewriter.ProgUtils.pred_ra_constr_qual_ident loc qual_ident
                  in

                  let assume_stmt =
                    let new_chunk =
                      let new_chunk_expr_list =
                        match c.call_decl.call_decl_kind with
                        | Pred ->
                            [
                              Expr.mk_int 1;
                              Expr.mk_tuple
                                (List.drop args (List.length pred_in_types));
                            ]
                        | Invariant ->
                            [
                              Expr.mk_tuple
                                (List.drop args (List.length pred_in_types));
                            ]
                        | _ ->
                            Error.error loc
                              "Internal error: Expected a predicate or \
                               invariant"
                      in

                      Expr.mk_app ~loc ~typ:heap_elem_type
                        (Expr.DataConstr pred_ra_constr) new_chunk_expr_list
                    in

                    Stmt.mk_assume_expr ~loc
                      ~cmnt:
                        ((match cmnt with None -> "" | Some cmnt -> cmnt)
                        ^ "\nassume: "
                        ^ Stdlib.Format.asprintf "%a" Expr.pr
                            (Expr.mk_binder Forall univ_vars_list
                              (Expr.mk_impl (Expr.mk_and conds) expr)))
                      (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
                         (Expr.mk_impl ~loc
                            (* m1(a,b,c) && l == f1(a, b, c) *)
                            (Expr.mk_and ~loc conds)
                            (* pred$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                            (Expr.mk_app ~loc ~typ:Type.bool
                               (Expr.Var pred_heapchunk_operator)
                               [
                                 Expr.mk_maplookup ~loc pred_heap_expr
                                   (Expr.mk_tuple
                                      (List.take args
                                         (List.length pred_in_types)));
                                 new_chunk;
                               ])))
                  in

                  Rewriter.return assume_stmt
              | _ -> Error.error loc "Expected a predicate definition")
          | _ -> unsupported_expr_error expr)
end

module TrnslExhale = struct
  let rec rewriter_user_annot_elim_exists_from_exhales (stmt : Stmt.t) :
      (Stmt.t, expr option) Rewriter.t_ext =
    let open Rewriter.Syntax in
    let rec find_existentials (expr : expr) : var_decl list =
      match expr with
      | Binder (Exists, var_decls, trgs, e, _) ->
          var_decls @ find_existentials e
      | Binder (_, var_decls, trgs, e, _) -> find_existentials e
      | App (_, exprs, _) -> List.concat_map exprs ~f:find_existentials
    in

    let subst_existentials (expr : expr) (subst_map : expr qual_ident_map) :
        expr =
      let rec elim_exists (expr : expr) subst_map : expr =
        match expr with
        | Binder (Exists, var_decls, trgs, e, _) ->
            let all_existentials_exist =
              List.for_all var_decls ~f:(fun var_decl ->
                  Map.mem subst_map (QualIdent.from_ident var_decl.var_name))
            in

            if not all_existentials_exist then
              Error.internal_error (Expr.to_loc expr)
                "Expected all existentials to be matched up"
            else e
        | Binder (b, var_decls, trgs, e, expr_attr) ->
            let e = elim_exists e subst_map in
            Binder (b, var_decls, trgs, e, expr_attr)
        | App (constr, exprs, expr_attr) ->
            let exprs = List.map exprs ~f:(fun e -> elim_exists e subst_map) in
            App (constr, exprs, expr_attr)
      in

      let expr = Expr.alpha_renaming expr subst_map in
      elim_exists expr subst_map
    in

    match stmt.stmt_desc with
    | Basic (Spec (Exhale, spec)) -> (
        let* prev_expr = Rewriter.current_user_state in
        let* () = Rewriter.set_user_state None in

        Logs.debug (fun m ->
            m
              "Rewrites.HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales: \
               prev_expr: %a; exhale_expr: %a"
              (Util.Print.pr_option Expr.pr)
              prev_expr Expr.pr spec.spec_form);

        let exhale_expr = spec.spec_form in
        match prev_expr with
        | None -> Rewriter.return stmt
        | Some prev_expr -> (
            Logs.debug (fun m ->
                m
                  "Rewrites.HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales: \
                   prev_expr: %a; exhale_expr: %a"
                  Expr.pr prev_expr Expr.pr exhale_expr);
            let existential_vars = find_existentials exhale_expr in

            match match_up_expr spec.spec_form prev_expr existential_vars with
            | None -> Rewriter.return stmt
            | Some var_map ->
                let subst_map =
                  Map.map var_map ~f:(fun (var_decl, expr) -> expr)
                in
                let subst_map =
                  (Map.map_keys_exn (module QualIdent)) subst_map
                    ~f:(fun ident -> QualIdent.from_ident ident)
                in
                let spec_form = subst_existentials exhale_expr subst_map in

                let spec = { spec with spec_form } in

                Rewriter.return
                  { stmt with stmt_desc = Basic (Spec (Exhale, spec)) }))
    | Basic (Spec (Assert, spec)) -> (
        let* prev_expr = Rewriter.current_user_state in

        let* () = Rewriter.set_user_state (Some spec.spec_form) in

        let assert_expr = spec.spec_form in
        match prev_expr with
        | None -> Rewriter.return stmt
        | Some prev_expr -> (
            Logs.debug (fun m ->
                m
                  "Rewrites.HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales \
                   (assert): prev_expr: %a; assert_expr: %a"
                  Expr.pr prev_expr Expr.pr assert_expr);
            let existential_vars = find_existentials assert_expr in

            match match_up_expr spec.spec_form prev_expr existential_vars with
            | None ->
                Logs.debug (fun m ->
                    m
                      "Rewrites.HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales \
                       (assert): No match up");
                Rewriter.return stmt
            | Some var_map ->
                let subst_map =
                  Map.map var_map ~f:(fun (var_decl, expr) -> expr)
                in
                let subst_map =
                  (Map.map_keys_exn (module QualIdent)) subst_map
                    ~f:(fun ident -> QualIdent.from_ident ident)
                in
                let spec_form = subst_existentials assert_expr subst_map in

                Logs.debug (fun m ->
                    m
                      "Rewrites.HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales \
                       (assert): spec_form: %a"
                      Expr.pr spec_form);

                let spec = { spec with spec_form } in

                Rewriter.return
                  { stmt with stmt_desc = Basic (Spec (Assert, spec)) }))
    | Basic _ ->
        let* () = Rewriter.set_user_state None in
        Rewriter.return stmt
    | _ ->
        (* let* () = Rewriter.set_user_state None in *)
        Rewriter.Stmt.descend stmt
          ~f:rewriter_user_annot_elim_exists_from_exhales

  module WitnessComputation = struct
    let rec find_witnesses_elim_exists (expr : expr) : (expr * expr list) Rewriter.t =
      elim_a { univ_vars = []; triggers = [] } [] expr

    and elim_a (universal_quants : universal_quants) (conds : conditions)
        (expr : expr) : (expr * expr list) Rewriter.t =
      let open Rewriter.Syntax in
      if%bind Rewriter.ProgUtils.is_expr_pure expr then Rewriter.return (expr, [])
      else
        match expr with
        | App (Ite, [ c; e1; e2 ], expr_attr) ->
            let* (e1, wtns_specs1) = elim_a universal_quants (c :: conds) e1 in

            let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
            let* (e2, wtns_specs2) = elim_a universal_quants (not_c :: conds) e2 in

            Rewriter.return (
              (Expr.App (Ite, [ c; e1; e2 ], expr_attr)), 
              wtns_specs1 @ wtns_specs2
            )
        | App (Impl, [ c; e2 ], expr_attr) ->
            let+ e2, wtns_specs = elim_a universal_quants (c :: conds) e2 in
            Expr.App (Impl, [ c; e2 ], expr_attr), wtns_specs
        | App (And, e_list, expr_attr) ->
            let* e_wtns_specs_list =
              Rewriter.List.map e_list ~f:(fun e ->
                  elim_a universal_quants conds e)
            in

            let e_list, wtns_specs = List.unzip e_wtns_specs_list in

            Rewriter.return (
              (Expr.App (And, e_list, expr_attr)), 
              (List.concat wtns_specs)
            )
        | Binder (Forall, var_decls, trgs, e, expr_attr) ->
            let universal_quants =
              let new_quants =
                List.map var_decls ~f:(fun var_decl ->
                    (var_decl.var_name, var_decl))
              in
              {
                univ_vars = universal_quants.univ_vars @ new_quants;
                triggers =
                  (match universal_quants.triggers with
                  | [] -> trgs
                  | _ ->
                      List.concat_map universal_quants.triggers ~f:(fun trigs ->
                          List.map trgs ~f:(fun trg -> trigs @ trg)));
              }
            in

            let* e, wtns_specs = elim_a universal_quants conds e in

            Rewriter.return (
              (Expr.Binder (Forall, var_decls, trgs, e, expr_attr)),
              wtns_specs
            )
        | _ -> elim_a1 universal_quants conds expr

    and elim_a1 (univ_vars : universal_quants) (univ_conds : conditions)
        (expr : expr) : (expr * expr list) Rewriter.t =
      let open Rewriter.Syntax in
      match expr with
      | Binder (Exists, var_decls, trgs, e, expr_attr) ->
          let loc =  expr_attr.expr_loc in
          let var_decls_skolem_idents = 
            List.map var_decls ~f:(
              fun vd ->
                (vd, ident_to_skolem_fn_ident ~loc vd.var_name)
            )
          in

          let* (witnesses : (conditions * expr option) list ident_map) =
            let init_map =
              List.fold var_decls
                ~init:(Map.empty (module Ident))
                ~f:(fun map var_decl ->
                  Map.add_exn map ~key:var_decl.var_name ~data:[])
            in

            elim_a0 univ_vars var_decls (univ_conds, []) e init_map
          in

          (* Sanitizing witnesses: 
          * a. getting rid of expr option; and
          * b. filtering empty lists [] from map *)
          let witnesses : (conditions * expr) list ident_map =
              let witnesses : (conditions * expr) list ident_map = 
                Map.map witnesses ~f:(fun cnd_expr_optn_list ->
                  List.filter_map cnd_expr_optn_list ~f:(fun (cnd, expr_optn) -> 
                    match expr_optn with
                    | None -> None
                    | Some e -> Some (cnd, e)
                  )
                )
              in

              let witnesses : (conditions * expr) list ident_map = 
                Map.filter witnesses ~f:(fun cnd_expr_list ->
                  not @@ List.is_empty cnd_expr_list
                )
              in 

            witnesses
          in

          let witnesses_local_vars_ident_set = 
            let (witnesses_local_vars_ident_set : IdentSet.t) =
              (* Folds over all existentials *)
              Map.fold witnesses ~init:(Set.empty (module Ident)) ~f:(
                fun ~key:_ ~data:cnd_expr_list accum_local_vars_set ->
                  
                (* Folds over all different witnesses computed for each existential *)
                List.fold cnd_expr_list ~init:accum_local_vars_set ~f:(
                  fun acc (cnds, e) ->

                  (* Folds over all path conditions for every witness *)
                  let path_conds_vars = List.fold cnds ~init:(Expr.local_vars e) ~f:(
                    fun accum cnd ->
                      Set.union accum (Expr.local_vars cnd)
                  )
                  in
                  Set.union acc path_conds_vars
                )
              )
            in

            witnesses_local_vars_ident_set
          in

          Logs.debug (fun m -> 
            let witnesses_local_vars_idents = Set.to_list witnesses_local_vars_ident_set in
            m 
            "TrnslExhale.WitnessComputation.elim_a1: witnesses_local_vars_ident: %a" 
              Ident.pr_list witnesses_local_vars_idents
          );

          let env_local_vars_ident =
            let univ_cond_locals_ident_set = 
              List.fold ~init:(Set.empty (module Ident)) univ_conds ~f:(fun accum expr ->
                Set.union accum (Expr.local_vars expr)
              )
            in

            let env_local_vars_ident_set = 
              Set.union univ_cond_locals_ident_set  witnesses_local_vars_ident_set 
            in

            let env_local_vars_ident = Set.to_list env_local_vars_ident_set in

            let env_local_non_skolems_vars_ident = List.filter env_local_vars_ident 
              ~f:(fun s ->
                (List.for_all var_decls 
                ~f:(fun vd ->
                  not @@ Ident.(vd.var_name = s)
                )) &&
                
                (List.for_all univ_vars.univ_vars 
                ~f:(fun (iden, _) ->
                  not @@ Ident.(iden = s)
                ))
              )
            in

            env_local_non_skolems_vars_ident
          in

          Logs.debug (fun m -> m 
          "TrnslExhale.WitnessComputation.elim_a1: env_local_vars_ident: %a" 
            Ident.pr_list env_local_vars_ident
          );

          let* env_local_var_decls =
            Rewriter.List.map env_local_vars_ident ~f:(fun iden ->
                let+ symbol =
                  Rewriter.find_and_reify (Ident.to_loc iden)
                    (QualIdent.from_ident iden)
                in
                match symbol with
                | VarDef v -> v.var_decl
                | _ ->
                    Error.error (Ident.to_loc iden)
                      "Expected a variable declaration")
          in

          Logs.debug (fun m -> m 
          "TrnslExhale.WitnessComputation.elim_a1: env_local_var_decls: %a" 
            Type.pr_var_decl_list env_local_var_decls
          );

          let env_local_var_decls_exprs = List.map env_local_var_decls ~f:(fun vd ->
            (vd, Expr.from_var_decl vd)  
          )

          in

          let witness_args_conds_exprs_map = 
            Map.mapi witnesses ~f:(fun ~key:iden ~data:witness_list ->
              let witness_arg_exprs =
                (List.map witness_list ~f:(fun (conds, witness) ->
                    let optn_arg =
                      {
                        Type.var_name =
                          Ident.fresh loc
                            ("witness_"
                            ^ Ident.to_string iden);
                        var_loc = loc;
                        var_type = Expr.to_type witness;
                        var_const = true;
                        var_ghost = false;
                        var_implicit = false;
                      }
                    in
                    
                    (optn_arg, conds, witness) 
                ))
              in
              
              witness_arg_exprs
            )
          in

          let skolem_vars_alpha_renaming_map = 
            List.fold var_decls_skolem_idents ~init:(Map.empty (module QualIdent)) ~f:(
              fun map (vd, skolem_id) -> (
                let skolemized_expr = 
                  let optn_args = begin
                    match Map.find witness_args_conds_exprs_map vd.var_name with
                    | None -> []
                    | Some arg_conds_expr_list -> 
                      List.map arg_conds_expr_list ~f:(fun (arg, cond, expr) -> expr)
                        @
                      List.map env_local_var_decls_exprs ~f:(fun (_vd, expr) -> expr) 
                    end 
                  in
                  Expr.mk_app ~loc ~typ:(vd.var_type) (Expr.Var (QualIdent.from_ident skolem_id)) optn_args

                in

                match (Map.add ~key:(QualIdent.from_ident vd.var_name) ~data:skolemized_expr map) with
                | `Ok map -> map
                | `Duplicate -> Error.internal_error loc "Duplicate existentially quantified var"
              )
            )
          in

          Logs.debug (fun m ->
              m
                "Rewrites.HeapsExplicitTrnsl.WitnessComputation.elim_a1: \
                 witness_map: %a"
                (Fmt.Dump.list (fun ppf (i, e) ->
                     Stdlib.Format.fprintf ppf "%a -> %a" Ident.pr i
                       (Fmt.Dump.list (fun ppf (c, e) ->
                            Stdlib.Format.fprintf ppf "%a -> %a"
                              (Util.Print.pr_list_comma Expr.pr)
                              c Expr.pr e))
                       e))
                (Map.to_alist witnesses));

          let* skolemized_exprs =
            Rewriter.List.map var_decls_skolem_idents ~f:(fun (var_decl, skolem_ident) ->
                let* postconds, optn_args =
                  match Map.find witness_args_conds_exprs_map var_decl.var_name with
                  | None | Some [] ->
                      let error =
                        ( Error.Verification,
                          Expr.to_loc expr,
                          "No witnesses could be computed for: "
                          ^ Ident.to_string var_decl.var_name )
                      in
                      Logs.warn (fun m -> m "%s" (Error.to_string error));
                      Rewriter.return ([], [])
                  | Some witness_arg_exprs ->
                      let postconds =
                        (List.map witness_arg_exprs ~f:(fun (optn_arg, conds, e) ->
                          (Expr.mk_impl (Expr.mk_and (univ_conds @ conds))
                            (Expr.mk_eq
                              (Expr.from_var_decl var_decl)
                              (Expr.from_var_decl optn_arg)
                            )
                          )
                        ))
                      in

                      let witness_optn_args = List.map witness_arg_exprs ~f:(
                        fun (vd, _, e) -> (vd, e)
                      ) in

                      let optn_args =
                        witness_optn_args @ env_local_var_decls_exprs
                      in

                      Rewriter.return (postconds, optn_args)
                in

                let postconds_sanitized = 
                  let skolem_vars_alpha_renaming_map_local =
                    Map.remove skolem_vars_alpha_renaming_map (QualIdent.from_ident var_decl.var_name) 
                  in
                  List.map postconds ~f:(
                    fun expr -> Expr.alpha_renaming expr skolem_vars_alpha_renaming_map_local
                  )
                in

                let+ expr =
                  generate_skolem_function univ_vars var_decl ~skolem_id:skolem_ident ~postconds:postconds_sanitized
                    ~optn_args ~loc:var_decl.var_loc
                in

                expr)
          in

          let* temp_skolem_var_decls__wtns_specs_list : (var_decl * expr) list =
            Rewriter.List.map (List.zip_exn var_decls skolemized_exprs)
              ~f:(fun (var_decl, skolem_expr) ->
                let skolem_wtns_var_tp =
                  if (List.is_empty univ_vars.univ_vars) then
                    var_decl.var_type
                  else
                    Type.mk_map loc (
                      Type.mk_prod loc 
                        (List.map univ_vars.univ_vars ~f:(fun (_, vd) -> vd.var_type))
                    )
                    (* ~~~> *)
                    var_decl.var_type
                in

                let temp_skolem_var_decl = {
                  var_decl with
                  var_name = Ident.fresh loc @@ 
                    "$skolem_expr_placeholder$$" ^ (Ident.to_string var_decl.var_name);
                  var_type = skolem_wtns_var_tp

                  }
                in

                let skolem_placeholder_var_def = (Module.VarDef { var_decl = temp_skolem_var_decl; var_init = None})

                in
                
                let+ _ =
                  Rewriter.introduce_typecheck_symbol ~loc  ~f:Typing.process_symbol skolem_placeholder_var_def
                in
              
                let wtns_constraint_expr = match univ_vars.univ_vars with
                | [] -> 
                  Expr.mk_eq ~loc
                      (Expr.from_var_decl temp_skolem_var_decl)
                      skolem_expr

                | _ -> 
                  Expr.mk_binder ~loc 
                    Forall (
                        List.map univ_vars.univ_vars ~f:(fun (_, vd) -> vd)
                        (* TODO: ^^^ Check if SMTLIB requires univ_vars need to be renamed when used in quantifiers. *)
                    ) (* :: *) (
                      Expr.mk_eq ~loc
                          (* skolem_var[ univ_vars ] *)
                          (Expr.mk_maplookup
                              (Expr.from_var_decl temp_skolem_var_decl)
                              (Expr.mk_tuple 
                                  (List.map univ_vars.univ_vars ~f:(fun (_, vd) -> (Expr.from_var_decl vd)))
                              )
                          )
                          (* == *)
                          skolem_expr
                    )
                in

                temp_skolem_var_decl, wtns_constraint_expr
            )
          in

          let temp_skolem_var_var_decls, wtns_specs_exprs = List.unzip temp_skolem_var_decls__wtns_specs_list
          in

          let renaming_map =
            List.fold2_exn var_decls temp_skolem_var_var_decls
              ~init:(Map.empty (module QualIdent))
              ~f:(fun map var_decl temp_skolem_var_decl ->
                Map.set map
                  ~key:(QualIdent.from_ident var_decl.var_name)
                  ~data:(
                    match univ_vars.univ_vars with
                    | [] -> Expr.from_var_decl temp_skolem_var_decl
                    | _ -> 
                      Expr.mk_maplookup 
                        (Expr.from_var_decl temp_skolem_var_decl) 
                        (* [ *)
                          (Expr.mk_tuple 
                            (List.map univ_vars.univ_vars ~f:(
                              fun (_, vd) -> Expr.from_var_decl vd
                            ))
                          )
                        (* ] *)
                  )
              )
          in

          Logs.debug (fun m ->
            m
              "Rewrites.HeapsExplicitTrnsl.WitnessComputation.elim_a1: \
               renaming_map: %a"
              (Fmt.Dump.list (fun ppf (qi, e) ->
                   Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr qi
                    Expr.pr e))
              (Map.to_alist renaming_map));

          let renaming_map_sanitized =
            (* Need to sanitize renaming_map if an existentially quantified expression occurs in a computed witness.
              eg: exists a, b :: x.f |-> (a, 1.) && a.f |-> (b, 1.)
              here renaming map would map
              a ~> (x.f)#0
              b ~> (a.f)#0

            This occurence of `a` in `renaming_map[b]` needs alpha-renamed. *)
            Map.map renaming_map ~f:(fun e ->
              Expr.alpha_renaming e renaming_map
            )
          in 

          let e = Expr.alpha_renaming e renaming_map_sanitized in
          let wtns_specs_exprs = 
            List.map wtns_specs_exprs ~f:(
              fun wtns_expr -> Expr.alpha_renaming wtns_expr renaming_map_sanitized
            )
          in
          let* e, wtns_specs = elim_a univ_vars univ_conds e in

          Rewriter.return (e, wtns_specs_exprs @ wtns_specs)
      | _ ->
          (* No existentials found *)
          Rewriter.return (expr, [])

    and elim_a0 (univ_vars : universal_quants) (exist_vars : var_decl list)
        ((univ_conds, exist_conds) : conditions * conditions) (expr : expr)
        (witness_map : (conditions * expr option) list ident_map) :
        (conditions * expr option) list ident_map Rewriter.t =
      let open Rewriter.Syntax in
      match expr with
      | App (And, e_list, _) ->
          let* witness_map =
            Rewriter.List.fold_left e_list ~init:witness_map ~f:(fun map e ->
                elim_a0 univ_vars exist_vars (univ_conds, exist_conds) e map)
          in

          Rewriter.return witness_map
      | App (Impl, [ c; e2 ], _) ->
          let* witness_map =
            elim_a0 univ_vars exist_vars
              (univ_conds, c :: exist_conds)
              e2 witness_map
          in

          Rewriter.return witness_map
      | App (Ite, [ c; e1; e2 ], _) ->
          let* witness_map =
            elim_a0 univ_vars exist_vars
              (univ_conds, c :: exist_conds)
              e1 witness_map
          in

          let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
          let* witness_map =
            elim_a0 univ_vars exist_vars
              (univ_conds, not_c :: exist_conds)
              e2 witness_map
          in

          Rewriter.return witness_map
      | App (Own, [ loc_expr; field_expr; val_expr ], _) ->
          let field_name =
            try Expr.to_qual_ident field_expr
            with _ ->
              Error.type_error (Expr.to_loc field_expr)
                "Expected field identifier."
          in

          let field_elem_type =
            match Expr.to_type field_expr with
            | App (Fld, [ tp_expr ], _) -> tp_expr
            | _ ->
                Error.type_error (Expr.to_loc field_expr)
                  "Expected field identifier."
          in

          let field_heap_name = field_heap_name field_name in
          let field_heap_type =
            Type.mk_map (Expr.to_loc expr) Type.ref field_elem_type
          in

          let concrete_expr =
            Expr.mk_maplookup
              (Expr.mk_var ~typ:field_heap_type
                 (QualIdent.from_ident field_heap_name))
              loc_expr
          in

          let relevant_vars =
            List.filter exist_vars ~f:(fun var_decl ->
                Set.exists (Expr.local_vars val_expr)
                  ~f:(Ident.equal var_decl.var_name))
          in

          let* witnesses =
            core_witness_comp relevant_vars concrete_expr val_expr false
          in

          Logs.debug (fun m ->
              m
                "Rewrites.HeapsExplicitTrnsl.WitnessComputation.elim_a0: \
                 witnesses: %a"
                (Fmt.Dump.list (fun ppf (i, e) ->
                     Stdlib.Format.fprintf ppf "%a -> %a" Ident.pr i Expr.pr e))
                (Map.to_alist witnesses));

          let witness_map =
            List.fold relevant_vars ~init:witness_map
              ~f:(fun witness_map var_decl ->
                let existing_val =
                  match Map.find witness_map var_decl.var_name with
                  | None -> []
                  | Some v -> v
                in

                let new_val =
                  (exist_conds, Map.find witnesses var_decl.var_name)
                  :: existing_val
                in

                Map.set witness_map ~key:var_decl.var_name ~data:new_val)
          in

          Rewriter.return witness_map
      | App (Var qual_ident, args, _) -> (
          let* symbol = Rewriter.find_and_reify (Expr.to_loc expr) qual_ident in

          match symbol with
          | CallDef c when Poly.(c.call_decl.call_decl_kind = Pred) ->
              let pred_heap = pred_heap_name qual_ident in
              let* pred_in_types =
                Rewriter.ProgUtils.pred_in_types qual_ident
              in
              let* pred_out_types =
                Rewriter.ProgUtils.pred_out_types qual_ident
              in

              let* pred_heap_type =
                Rewriter.ProgUtils.pred_heap_type qual_ident
              in
              let pred_heap_expr =
                Expr.mk_var (QualIdent.from_ident pred_heap) ~typ:pred_heap_type
              in

              let* pred_val_destr =
                Rewriter.ProgUtils.pred_ra_val_destr_qual_ident
                  (Expr.to_loc expr) qual_ident
              in

              let pred_heap_val =
                Expr.mk_app
                  ~typ:(Type.mk_prod (Expr.to_loc expr) pred_out_types)
                  (DataDestr pred_val_destr)
                  [
                    Expr.mk_maplookup pred_heap_expr
                      (Expr.mk_tuple
                         (List.take args (List.length pred_in_types)));
                  ]
              in

              let* pred_heap_expanded_type =
                Typing.ProcessTypeExpr.expand_type_expr
                  (Expr.to_type pred_heap_val)
              in

              Logs.debug (fun m ->
                  m
                    "Rewrites.HeapsExplicitTrnsl.WitnessComputation.elim_a0: \
                     pred_heap_expanded_type: %a"
                    Type.pr pred_heap_expanded_type);

              let pred_heap_val_expanded_typ =
                Expr.set_type pred_heap_val pred_heap_expanded_type
              in

              let concrete_exprs =
                List.mapi
                  (List.drop args (List.length pred_in_types))
                  ~f:(fun i _ ->
                    Expr.mk_tuple_lookup pred_heap_val_expanded_typ i)
              in

              let out_args_concrete_exprs =
                List.zip_exn
                  (List.drop args (List.length pred_in_types))
                  concrete_exprs
              in

              let* witness_map =
                Rewriter.List.fold_left out_args_concrete_exprs
                  ~init:witness_map
                  ~f:(fun witness_map (out_arg, concrete_expr) ->
                    let* witnesses =
                      core_witness_comp exist_vars concrete_expr out_arg true
                    in

                    let witness_map =
                      List.fold exist_vars ~init:witness_map
                        ~f:(fun witness_map var_decl ->
                          let existing_val =
                            Option.value
                              (Map.find witness_map var_decl.var_name)
                              ~default:[]
                          in

                          let new_val =
                            (exist_conds, Map.find witnesses var_decl.var_name)
                            :: existing_val
                          in

                          Map.set witness_map ~key:var_decl.var_name
                            ~data:new_val)
                    in

                    Rewriter.return witness_map)
              in

              Logs.debug (fun m ->
                  m
                    "Rewrites.HeapsExplicitTrnsl.WitnessComputation.elim_a0: \
                     witness_map: %a"
                    (Fmt.Dump.list (fun ppf (i, e) ->
                         Stdlib.Format.fprintf ppf "%a -> %a" Ident.pr i
                           (Fmt.Dump.list (fun ppf (c, e) ->
                                Stdlib.Format.fprintf ppf "%a -> %a"
                                  (Util.Print.pr_list_comma Expr.pr)
                                  c (Fmt.Dump.option Expr.pr) e))
                           e))
                    (Map.to_alist witness_map));

              Rewriter.return witness_map
          | _ -> Rewriter.return witness_map)
      | _ -> Rewriter.return witness_map

    and core_witness_comp (exists : var_decl list) (concrete_expr : expr)
        (given_expr : expr) (exact : bool) : expr ident_map Rewriter.t =
      let open Rewriter.Syntax in
      Logs.debug (fun m ->
          m
            "Rewrites.HeapsExplicitTrnsl.WitnessComputation.core_witness_comp: \
             exists: %a, concrete_expr: %a, given_expr: %a, exact: %b"
            (Fmt.Dump.list Ident.pr)
            (List.map exists ~f:(fun v -> v.var_name))
            Expr.pr concrete_expr Expr.pr given_expr exact);

      match exact with
      | false ->
          let ra_name =
            match Expr.to_type given_expr with
            | App (Var ra_name, [], _) -> QualIdent.pop ra_name
            | App (Data (ra_name, _), [], _) -> QualIdent.pop ra_name
            | tp ->
                Error.type_error (Expr.to_loc given_expr)
                  ("Expected an RA type; found: " ^ Type.to_string tp)
          in

          let* orig_name, ra_def, _ =
            Rewriter.find (Expr.to_loc given_expr) ra_name
          in

          if QualIdent.(orig_name = Predefs.lib_auth_mod_qual_ident) then
            match given_expr with
            | App (DataConstr constr_ident, exprs, _) ->
                if
                  Ident.(
                    QualIdent.unqualify constr_ident
                    = Predefs.lib_auth_frag_constr_ident)
                then
                  let auth_chunk =
                    Expr.mk_app
                      ~typ:(Expr.to_type (List.hd_exn exprs))
                      (Expr.DataDestr
                         (QualIdent.append ra_name
                            Predefs.lib_auth_frag_destr1_ident))
                      [ concrete_expr ]
                  in
                  core_witness_comp exists auth_chunk (List.hd_exn exprs) true
                  (* Error.error_simple "unimplemented" *)
                else Rewriter.return (Map.empty (module Ident))
            | _ ->
                Error.type_error (Expr.to_loc given_expr)
                  "Expected a data constructor."
          else if QualIdent.(orig_name = Predefs.lib_frac_mod_qual_ident) then
            match given_expr with
            | App (DataConstr constr_ident, exprs, _) ->
                if
                  Ident.(
                    QualIdent.unqualify constr_ident
                    = Predefs.lib_frac_chunk_constr_ident)
                then
                  let frac_chunk =
                    Expr.mk_app
                      ~typ:(Expr.to_type (List.hd_exn exprs))
                      (Expr.DataDestr
                         (QualIdent.append ra_name
                            Predefs.lib_frac_chunk_destr1_ident))
                      [ concrete_expr ]
                  in
                  core_witness_comp exists frac_chunk (List.hd_exn exprs) true
                else Rewriter.return (Map.empty (module Ident))
            | _ ->
                Error.type_error (Expr.to_loc given_expr)
                  "Expected a data constructor."
          else if QualIdent.(orig_name = Predefs.lib_agree_mod_qual_ident) then
            match given_expr with
            | App (DataConstr constr_ident, exprs, _) ->
                if
                  Ident.(
                    QualIdent.unqualify constr_ident
                    = Predefs.lib_agree_constr_ident)
                then
                  let agree_chunk =
                    Expr.mk_app
                      ~typ:(Expr.to_type (List.hd_exn exprs))
                      (Expr.DataDestr
                         (QualIdent.append ra_name
                            Predefs.lib_agree_destr1_ident))
                      [ concrete_expr ]
                  in
                  core_witness_comp exists agree_chunk (List.hd_exn exprs) true
                else Rewriter.return (Map.empty (module Ident))
            | _ ->
                Error.type_error (Expr.to_loc given_expr)
                  "Expected a data constructor."
          else Rewriter.return (Map.empty (module Ident))
      | true -> (
          match given_expr with
          | App (Var ident, [], _) ->
              if
                List.exists exists ~f:(fun var_decl ->
                    Poly.(QualIdent.from_ident var_decl.var_name = ident))
              then
                Rewriter.return
                  (Map.singleton
                     (module Ident)
                     (QualIdent.unqualify ident)
                     concrete_expr)
              else Rewriter.return (Map.empty (module Ident))
          | App (Tuple, exprs, _) ->
              let* witness_map =
                Rewriter.List.fold_left exprs
                  ~init:(Map.empty (module Ident))
                  ~f:(fun witness_map expr ->
                    let* new_witness_map =
                      core_witness_comp exists concrete_expr expr true
                    in

                    let witness_map =
                      Map.merge witness_map new_witness_map ~f:(fun ~key:_ ->
                        function
                        | `Both (w1, w2) -> Some w1
                        | `Left w1 -> Some w1
                        | `Right w2 -> Some w2)
                    in

                    Rewriter.return witness_map)
              in

              Rewriter.return witness_map
          | App (DataConstr qual_iden, exprs, _) ->
              let* destrs =
                Rewriter.ProgUtils.get_data_destrs_from_constr qual_iden
              in

              let* destrs =
                Rewriter.List.map destrs ~f:(fun destr ->
                    let+ destr_ret_type =
                      let* destr_symbol =
                        Rewriter.find_and_reify (Expr.to_loc given_expr) destr
                      in
                      match destr_symbol with
                      | DestrDef destr ->
                          Rewriter.return destr.destr_return_type
                      | _ ->
                          Error.error (Expr.to_loc given_expr)
                            "Expected a destructor definition"
                    in

                    (destr, destr_ret_type))
              in

              let destr_exprs =
                List.map2_exn destrs exprs ~f:(fun (destr, ret_typ) expr ->
                    Expr.mk_app ~typ:ret_typ (Expr.DataDestr destr) [ expr ])
              in

              let* witness_map =
                Rewriter.List.fold_left destr_exprs
                  ~init:(Map.empty (module Ident))
                  ~f:(fun witness_map destr_expr ->
                    let* new_witness_map =
                      core_witness_comp exists concrete_expr destr_expr true
                    in

                    let witness_map =
                      Map.merge witness_map new_witness_map ~f:(fun ~key:_ ->
                        function
                        | `Both (w1, w2) -> Some w1
                        | `Left w1 -> Some w1
                        | `Right w2 -> Some w2)
                    in

                    Rewriter.return witness_map)
              in

              Rewriter.return witness_map
          | _ -> Rewriter.return (Map.empty (module Ident)))
  end

  let rec rewriter_find_witness_elim_exists_from_exhale (stmt : Stmt.t) :
      Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    let loc = Stmt.to_loc stmt in
    match stmt.stmt_desc with
    | Basic (Spec (Exhale, spec)) ->
        let exhale_expr = spec.spec_form in
        let* elim_expr, wtns_specs =
          WitnessComputation.find_witnesses_elim_exists exhale_expr
        in

        Logs.debug (fun m -> m 
          "WitnessComputation.rewriter_find_witness_elim_exists_from_exhale: \n \
              init exhale_expr: %a \n \
              elim exhale_expr: %a
          "
            Expr.pr exhale_expr
            Expr.pr elim_expr
        );

        let spec = { spec with spec_form = elim_expr } in
        let exhale_stmt = { stmt with stmt_desc = Basic (Spec (Exhale, spec)) } in 

        let wtns_specs_stmts = List.map wtns_specs ~f:(
          fun spec_expr -> 
            Stmt.mk_assume_expr ~loc spec_expr 
              ~cmnt:("Witness binding `assume`, for existentials during exhale.")
        )
        in 

        Rewriter.return (
          Stmt.mk_block_stmt ~loc (wtns_specs_stmts @ [exhale_stmt])
        )

    | Basic (Spec (Assert, spec)) ->
        let assert_expr = spec.spec_form in
        let* elim_expr, wtns_specs =
          WitnessComputation.find_witnesses_elim_exists assert_expr
        in

        let spec = { spec with spec_form = elim_expr } in
        let assert_stmt = { stmt with stmt_desc = Basic (Spec (Assert, spec)) } in 

        let wtns_specs_stmts = List.map wtns_specs ~f:(
          fun spec_expr -> 
            Stmt.mk_assume_expr ~loc spec_expr
              ~cmnt:("Witness binding `assume`, for existentials during assert.")
        )
        in 

        Rewriter.return (
          Stmt.mk_block_stmt ~loc (wtns_specs_stmts @ [assert_stmt])
        )

    | _ ->
        Rewriter.Stmt.descend stmt
          ~f:rewriter_find_witness_elim_exists_from_exhale

  let rec trnsl_exhale_expr ?cmnt ?spec_error ~loc (expr : expr) :
      Stmt.t Rewriter.t =
    ParseAssertionLang.parse_a ?cmnt ?spec_error ~loc [] expr
      ~parse_a0:trnsl_exhale_a0

  and trnsl_exhale_a0 ?cmnt ?(spec_error = []) ~loc
      (universal_quants : universal_quants) (conds : conditions) (expr : expr) :
      Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    let univ_quants_list = universal_quants.univ_vars in
    let univ_vars_list =
      List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl)
    in

    match expr with
    | App (Own, [ e1; e2; e3 ], _) ->
        (* forall a, b, c :: m1(a, b, c) ==> own(f1(a, b, c), field, f2(a, b, c))

           ===>

           // asserting injectivity of functions
           assert forall a, b, c, a', b', c' :: m1(a, b, c) && m1(a', b', c') ==> f1(a, b, c) == f1(a', b', c') ==> (a == a' && b == b' && c == c')

           havoc(field$Heap2);

           assert forall l: Ref ::
             m1(inv(l)#0, inv(l)#1, inv(l)#2) && l == f1(inv(l)#0, inv(l)#1, inv(l)#2) ?
                 field$Heap2[l] == field.frame( field$Heap[l], f2(a, b, c) ) :
               field$Heap2[l] == field$Heap[l]

           field$Heap := field$Heap2
           assert field.valid(field$Heap)
        *)
        let field_type =
          match Expr.to_type e2 with
          | App (Fld, [ tp_expr ], _) -> tp_expr
          | _ -> Error.type_error (Expr.to_loc e2) "Expected field identifier."
        in

        let field_name = Expr.to_qual_ident e2 in
        let field_heap_name = field_heap_name field_name in
        let field_heap_qual_ident = QualIdent.from_ident field_heap_name in
        let field_heap_expr =
          Expr.mk_var
            ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type)
            field_heap_qual_ident
        in

        let field_heap2_name = field_heap_name2 field_name in
        let field_heap2_qual_ident = QualIdent.from_ident field_heap2_name in
        let field_heap2_expr =
          Expr.mk_var
            ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type)
            field_heap2_qual_ident
        in

        let* (field_heapchunk_operator : qual_ident) =
          Rewriter.ProgUtils.get_field_utils_frame (Expr.to_loc e2) field_name
        in

        let* (field_heap_valid_fn : qual_ident) =
          Rewriter.ProgUtils.get_field_utils_valid (Expr.to_loc e2) field_name
        in

        let l_var =
          Type.
            {
              var_name = Ident.fresh (Expr.to_loc expr) "l";
              var_loc = Expr.to_loc expr;
              var_type = Type.ref;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
        in

        let l_expr =
          Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name)
        in

        let* inv_fn_expr =
          generate_inv_function ~loc universal_quants conds e1 ~arg_expr:l_expr
        in

        let inv_exprs =
          List.mapi univ_vars_list ~f:(fun index var_decl ->
              Expr.mk_tuple_lookup inv_fn_expr index)
        in

        (* exhale forall i, j :: { v(i,j) } own(f(i, j), fld, v(i, j))
          *   ~~>
          * forall i, j :: { v(i,j) } 
          *  v[
          *      i <- inv(f(i, j), i, j)#0, 
          *      j <- inv(f(i, j), i, j)#1
          *  ] (var substitution)
          *    = 
          *  v(i, j) *)
        let* forward_trigger_assertion =
          let inv_fn_qi = (match inv_fn_expr with
            | App ((Expr.Var inv_fn_qi), args, _) -> inv_fn_qi
            | _ -> 
              Error.internal_error loc "Expected inv function call (e/own)"            
          ) in

          let+ env_local_var_decls =
            compute_env_local_var_decls ~loc e1 conds universal_quants
          in
          
          let inv_expr = 
            Expr.mk_app ~loc 
              ~typ:(Type.mk_prod loc 
                (List.map univ_vars_list ~f:(fun var_decl -> var_decl.var_type))
              )  
              (Expr.Var inv_fn_qi) 
                (e1 :: (List.map env_local_var_decls ~f:Expr.from_var_decl))
          in 

          (* i ~> inv(f(i, j), i, j)#0
            * j ~> inv(f(i, j), i, j)#1*)
          let renaming_map =
            List.foldi univ_vars_list 
              ~init:(Map.empty (module QualIdent))
              ~f:(fun index map var_decl ->
                Map.set map
                  ~key:(QualIdent.from_ident var_decl.var_name)
                  ~data:(Expr.mk_tuple_lookup ~loc inv_expr index))
          in
          let expr = Expr.alpha_renaming e3 renaming_map 
          
          in

          Stmt.mk_assume_expr ~loc  ~cmnt:"forward_trigger_assertion" (
            Expr.mk_binder ~trigs:universal_quants.triggers ~loc ~typ:Type.bool Forall univ_vars_list
            (Expr.mk_eq ~loc expr e3)
          )
        in


        let alpha_renaming_map =
          List.fold2_exn univ_vars_list inv_exprs
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl expr ->
              Map.set map
                ~key:(QualIdent.from_ident var_decl.var_name)
                ~data:expr)
        in

        let e1_subst = Expr.alpha_renaming e1 alpha_renaming_map in
        let e3_subst = Expr.alpha_renaming e3 alpha_renaming_map in

        let conds_subst =
          List.map conds ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in

        let havoc_stmt = Stmt.mk_havoc ~loc field_heap2_qual_ident in
        let assume_stmt =
          let l_eq_e1_expr = Expr.mk_eq l_expr e1_subst in

          Stmt.mk_assume_expr ~loc
            ~cmnt:
                 ((match cmnt with None -> "" | Some cmnt -> cmnt ^ "\n")
                 ^ "exhale: "
                 ^ Stdlib.Format.asprintf "%a" Expr.pr
                     (Expr.mk_binder Forall univ_vars_list
                        (Expr.mk_impl (Expr.mk_and conds) expr)))
            (Expr.mk_binder
               ~trigs:
                 [
                   [ Expr.mk_maplookup ~loc field_heap2_expr l_expr ];
                   [ Expr.mk_maplookup ~loc field_heap_expr l_expr ];
                 ]
               ~loc ~typ:Type.bool Forall [ l_var ]
               (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                  [
                    (* m1(a,b,c) && l == f1(a, b, c) *)
                    Expr.mk_and ~loc (l_eq_e1_expr :: conds_subst);
                    (* field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                    Expr.mk_eq ~loc
                      (Expr.mk_maplookup ~loc field_heap2_expr e1_subst)
                      (Expr.mk_app ~loc ~typ:field_type
                         (Expr.Var field_heapchunk_operator)
                         [
                           Expr.mk_maplookup ~loc field_heap_expr l_expr;
                           e3_subst;
                         ]);
                    (* field$Heap2[l] == field$Heap[l] *)
                    Expr.mk_eq ~loc
                      (Expr.mk_maplookup ~loc field_heap2_expr l_expr)
                      (Expr.mk_maplookup ~loc field_heap_expr l_expr);
                  ]))
        in

        (* field$Heap := field$Heap2 *)
        let eq_stmt =
          Stmt.mk_assign ~loc [ field_heap_expr ] field_heap2_expr
        in

        let assert_heap_valid =
          Stmt.mk_assert_expr ~loc ~spec_error
            (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var field_heap_valid_fn)
               [ field_heap_expr ])
        in

        let* injectivity_assertion =
          generate_injectivity_assertions ~loc universal_quants conds e1
        in

        let stmts_list =
          match univ_quants_list with
          | [] -> []
          | _ -> [ injectivity_assertion ]
        in

        let stmts_list =
          stmts_list @ [ havoc_stmt; assume_stmt; forward_trigger_assertion; eq_stmt; assert_heap_valid ]
        in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt
    | App (AUPred call_qual_ident, token :: args, _)
    | App (AUPredCommit call_qual_ident, token :: args, _) ->
        let loc = Expr.to_loc expr in
        let* heap_elem_type_qual_iden =
          Rewriter.ProgUtils.get_au_utils_rep_type loc call_qual_ident
        in

        let heap_elem_type = Type.mk_var loc heap_elem_type_qual_iden in

        let call_name = call_qual_ident in
        let au_heap_name = au_heap_name call_name in
        let au_heap_qual_ident = QualIdent.from_ident au_heap_name in
        let au_heap_expr =
          Expr.mk_var
            ~typ:(Type.mk_map loc Type.ref heap_elem_type)
            au_heap_qual_ident
        in

        let au_heap2_name = au_heap_name2 call_name in
        let au_heap2_qual_ident = QualIdent.from_ident au_heap2_name in
        let au_heap2_expr =
          Expr.mk_var
            ~typ:(Type.mk_map loc Type.ref heap_elem_type)
            au_heap2_qual_ident
        in

        let* (au_heapchunk_operator : qual_ident) =
          Rewriter.ProgUtils.get_au_utils_frame loc call_name
        in

        let* (au_heap_valid_fn : qual_ident) =
          Rewriter.ProgUtils.get_au_utils_valid loc call_name
        in

        let* au_ra_uncommitted_constr =
          Rewriter.ProgUtils.au_ra_uncommitted_constr_qual_ident loc
            call_qual_ident
        in
        let* au_ra_committed_constr =
          Rewriter.ProgUtils.au_ra_committed_constr_qual_ident loc
            call_qual_ident
        in

        let havoc_stmt = Stmt.mk_havoc ~loc au_heap2_qual_ident in

        let new_token_var =
          {
            Type.var_name = Ident.fresh loc "tok";
            var_loc = loc;
            var_type = Type.atomic_token;
            var_const = false;
            var_ghost = false;
            var_implicit = false;
          }
        in

        let new_token_expr = Expr.from_var_decl new_token_var in

        let* inv_fn_expr =
          generate_inv_function ~loc universal_quants conds token
            ~arg_expr:new_token_expr
        in

        let inv_exprs =
          List.mapi univ_vars_list ~f:(fun index var_decl ->
              Expr.mk_tuple_lookup inv_fn_expr index)
        in

        (* exhale forall i, j :: { v(i,j) } AUPred(proc, gamma(i,j), (a_1, ... a_k)(i, j))
        *   ~~>
        * forall i, j :: { v(i,j) } 
        *  (a_1, ... a_k)[
        *      i <- inv(f(i, j), i, j)#0, 
        *      j <- inv(f(i, j), i, j)#1
        *  ] (var substitution)
        *    = 
        *  (a_1, ... a_k)(i, j) *)
        let* forward_trigger_assertion =
          let inv_fn_qi = (match inv_fn_expr with
            | App ((Expr.Var inv_fn_qi), args, _) -> inv_fn_qi
            | _ -> 
              Error.internal_error loc "Expected inv function call (e/au)"            
          ) in

          let+ env_local_var_decls =
            compute_env_local_var_decls ~loc token conds universal_quants
          in
          
          let inv_expr = 
            Expr.mk_app ~loc 
              ~typ:(Type.mk_prod loc 
                (List.map univ_vars_list ~f:(fun var_decl -> var_decl.var_type))
              )  
              (Expr.Var inv_fn_qi) 
                (token :: (List.map env_local_var_decls ~f:Expr.from_var_decl))
          in 

          (* i ~> inv(f(i, j), i, j)#0
            * j ~> inv(f(i, j), i, j)#1*)
          let renaming_map =
            List.foldi univ_vars_list 
              ~init:(Map.empty (module QualIdent))
              ~f:(fun index map var_decl ->
                Map.set map
                  ~key:(QualIdent.from_ident var_decl.var_name)
                  ~data:(Expr.mk_tuple_lookup ~loc inv_expr index))
          in
          let expr = Expr.alpha_renaming (Expr.mk_tuple args) renaming_map 
          
          in

          Stmt.mk_assume_expr ~loc  ~cmnt:"forward_trigger_assertion" (
            Expr.mk_binder ~trigs:universal_quants.triggers ~loc ~typ:Type.bool Forall univ_vars_list
            (Expr.mk_eq ~loc expr (Expr.mk_tuple args))
          )
        in

        let alpha_renaming_map =
          List.fold2_exn univ_vars_list inv_exprs
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl expr ->
              Map.set map
                ~key:(QualIdent.from_ident var_decl.var_name)
                ~data:expr)
        in

        let token_subst = Expr.alpha_renaming token alpha_renaming_map in
        let args_subst =
          List.map args ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in
        let conds_subst =
          List.map conds ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in

        let assume_stmt =
          let token_var_eq_given_token =
            Expr.mk_eq new_token_expr token_subst
          in

          let new_chunk =
            match expr with
            | App (AUPred _, _, _) ->
                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_uncommitted_constr)
                  [ Expr.mk_tuple args_subst ]
            | App (AUPredCommit _, _, _) ->
                let ret_val = List.last_exn args_subst in
                let call_args = List.drop_last_exn args_subst in

                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_committed_constr)
                  [ Expr.mk_tuple call_args; ret_val ]
            | _ -> Error.error loc "Internal error"
          in

          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt)
              ^ "\nexhale: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                    (Expr.mk_impl (Expr.mk_and conds) expr)))
            (Expr.mk_binder
               ~trigs:
                 [
                   [ Expr.mk_maplookup ~loc au_heap2_expr new_token_expr ];
                   [ Expr.mk_maplookup ~loc au_heap_expr new_token_expr ];
                 ]
               ~loc ~typ:Type.bool Forall [ new_token_var ]
               (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
                  (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                     [
                       (* m1(a,b,c) && l == f1(a, b, c) *)
                       Expr.mk_and ~loc (token_var_eq_given_token :: conds_subst);
                       (* au$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                       Expr.mk_eq ~loc
                         (Expr.mk_maplookup ~loc au_heap2_expr token_subst)
                         (Expr.mk_app ~loc ~typ:heap_elem_type
                            (Expr.Var au_heapchunk_operator)
                            [
                              Expr.mk_maplookup ~loc au_heap_expr new_token_expr;
                              new_chunk;
                            ]);
                       (* pred$Heap2[l] == pred$Heap[l] *)
                       Expr.mk_eq ~loc
                         (Expr.mk_maplookup ~loc au_heap2_expr new_token_expr)
                         (Expr.mk_maplookup ~loc au_heap_expr new_token_expr);
                     ])))
        in

        (* pred$Heap := pred$Heap2 *)
        let eq_stmt = Stmt.mk_assign ~loc [ au_heap_expr ] au_heap2_expr in

        let assert_heap_valid =
          Stmt.mk_assert_expr ~loc ~spec_error
            (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var au_heap_valid_fn)
               [ au_heap_expr ])
        in

        let* injectivity_assertion =
          generate_injectivity_assertions ~loc universal_quants conds token
        in

        let stmts_list =
          match univ_quants_list with
          | [] -> []
          | _ -> [ injectivity_assertion ]
        in

        let stmts_list =
          stmts_list @ [ havoc_stmt; assume_stmt; forward_trigger_assertion; eq_stmt; assert_heap_valid ]
        in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt
    | e -> (
        let* is_e_pure = Rewriter.ProgUtils.is_expr_pure e in
        if is_e_pure then
          let assert_expr =
            Expr.mk_binder ~loc ~typ:Type.bool ~trigs:universal_quants.triggers
              Forall
              (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d))
              (Expr.mk_impl (Expr.mk_and conds) e)
          in

          let assert_stmt =
            Stmt.mk_assert_expr ~loc
              ~cmnt:
                ((match cmnt with None -> "" | Some cmnt -> cmnt)
                ^ "\nexhale: "
                ^ Stdlib.Format.asprintf "%a" Expr.pr
                    (Expr.mk_binder Forall univ_vars_list
                      (Expr.mk_impl (Expr.mk_and conds) expr)))
              ~spec_error assert_expr
          in
          (* let assume_stmt = (Stmt.mk_assume_expr ~loc assert_expr) in *)
          (* Rewriter.return (Stmt.mk_block_stmt ~loc [assume_stmt; assert_stmt]) *)
          Rewriter.return assert_stmt
        else
          match e with
          | App (Var qual_ident, args, _) -> (
              let* symbol = Rewriter.find_and_reify loc qual_ident in
              match symbol with
              | CallDef c
                when Poly.(
                       c.call_decl.call_decl_kind = Pred
                       || c.call_decl.call_decl_kind = Invariant) ->
                  let* heap_elem_type_qual_iden =
                    Rewriter.ProgUtils.get_pred_utils_rep_type loc qual_ident
                  in

                  let heap_elem_type =
                    Type.mk_var loc heap_elem_type_qual_iden
                  in

                  let pred_name = qual_ident in
                  let pred_heap_name = pred_heap_name pred_name in
                  let pred_heap_qual_ident =
                    QualIdent.from_ident pred_heap_name
                  in
                  let pred_heap_expr =
                    Expr.mk_var
                      ~typ:(Type.mk_map loc Type.ref heap_elem_type)
                      pred_heap_qual_ident
                  in

                  let pred_heap2_name = pred_heap_name2 pred_name in
                  let pred_heap2_qual_ident =
                    QualIdent.from_ident pred_heap2_name
                  in
                  let pred_heap2_expr =
                    Expr.mk_var
                      ~typ:(Type.mk_map loc Type.ref heap_elem_type)
                      pred_heap2_qual_ident
                  in

                  let* (pred_heapchunk_operator : qual_ident) =
                    Rewriter.ProgUtils.get_pred_utils_frame loc pred_name
                  in

                  let* (pred_heap_valid_fn : qual_ident) =
                    Rewriter.ProgUtils.get_pred_utils_valid loc pred_name
                  in

                  let* pred_in_types =
                    Rewriter.ProgUtils.pred_in_types qual_ident
                  in

                  let* pred_out_types =
                    Rewriter.ProgUtils.pred_out_types qual_ident
                  in

                  let* pred_ra_constr =
                    Rewriter.ProgUtils.pred_ra_constr_qual_ident loc qual_ident
                  in

                  let in_vars =
                    List.map pred_in_types ~f:(fun tp ->
                        {
                          Type.var_name = Ident.fresh loc "in";
                          var_loc = Expr.to_loc e;
                          var_type = tp;
                          var_const = false;
                          var_ghost = false;
                          var_implicit = false;
                        })
                  in

                  let in_vars_exprs =
                    List.map in_vars ~f:(fun v -> Expr.from_var_decl v)
                  in
                  let in_vars_tuple = Expr.mk_tuple in_vars_exprs in

                  let actual_arg_in_exprs =
                    List.take args (List.length pred_in_types)
                  in
                  let actual_arg_out_exprs =
                    List.drop args (List.length pred_in_types)
                  in

                  let* inv_fn_expr =
                    generate_inv_function ~loc universal_quants conds
                      (Expr.mk_tuple actual_arg_in_exprs)
                      ~arg_expr:in_vars_tuple
                  in

                  let inv_exprs =
                    List.mapi univ_vars_list ~f:(fun index var_decl ->
                        Expr.mk_tuple_lookup inv_fn_expr index)
                  in

                  (* exhale forall i, j :: { v(i,j) } pred(ins(i, j); outs(i, j))
                  *   ~~>
                  * forall i, j :: { v(i,j) } 
                  *  outs[
                  *      i <- inv(f(i, j), i, j)#0, 
                  *      j <- inv(f(i, j), i, j)#1
                  *  ] (var substitution)
                  *    = 
                  *  outs(i, j) *)
                  let* forward_trigger_assertion =
                    let inv_fn_qi_opt = (match inv_fn_expr with
                      | App ((Expr.Var inv_fn_qi), args, _) -> 
                        Some inv_fn_qi
                      | _ -> 
                        None

                        (* Error.internal_error loc "Expected inv function call (e/pred)"*)
                    ) in

                    begin match inv_fn_qi_opt with
                    | None -> 
                      Rewriter.return (Stmt.mk_skip ~loc)

                    | Some inv_fn_qi ->
                      let+ env_local_var_decls =
                        compute_env_local_var_decls ~loc (Expr.mk_tuple actual_arg_in_exprs) conds universal_quants
                      in
                      
                      let inv_expr = 
                        Expr.mk_app ~loc 
                          ~typ:(Type.mk_prod loc 
                            (List.map univ_vars_list ~f:(fun var_decl -> var_decl.var_type))
                          )  
                          (Expr.Var inv_fn_qi) 
                            ((Expr.mk_tuple actual_arg_in_exprs) :: (List.map env_local_var_decls ~f:Expr.from_var_decl))
                      in 
            
                      (* i ~> inv(f(i, j), i, j)#0
                      * j ~> inv(f(i, j), i, j)#1*)
                      let renaming_map =
                        List.foldi univ_vars_list 
                          ~init:(Map.empty (module QualIdent))
                          ~f:(fun index map var_decl ->
                            Map.set map
                              ~key:(QualIdent.from_ident var_decl.var_name)
                              ~data:(Expr.mk_tuple_lookup ~loc inv_expr index))
                      in
                      let expr = Expr.alpha_renaming (Expr.mk_tuple actual_arg_out_exprs) renaming_map 
                      
                      in
            
                      Stmt.mk_assume_expr ~loc  ~cmnt:"forward_trigger_assertion" (
                        Expr.mk_binder ~trigs:universal_quants.triggers ~loc ~typ:Type.bool Forall univ_vars_list
                        (Expr.mk_eq ~loc expr (Expr.mk_tuple actual_arg_out_exprs))
                      )
                    end
                  in

                  let alpha_renaming_map =
                    List.fold2_exn univ_vars_list inv_exprs
                      ~init:(Map.empty (module QualIdent))
                      ~f:(fun map var_decl expr ->
                        Map.set map
                          ~key:(QualIdent.from_ident var_decl.var_name)
                          ~data:expr)
                  in

                  let actual_arg_in_exprs_subst =
                    List.map actual_arg_in_exprs ~f:(fun e ->
                        Expr.alpha_renaming e alpha_renaming_map)
                  in
                  let actual_arg_in_exprs_subst_tuple =
                    Expr.mk_tuple actual_arg_in_exprs_subst
                  in
                  let actual_arg_out_exprs_subst =
                    List.map actual_arg_out_exprs ~f:(fun e ->
                        Expr.alpha_renaming e alpha_renaming_map)
                  in
                  let conds_subst =
                    List.map conds ~f:(fun e ->
                        Expr.alpha_renaming e alpha_renaming_map)
                  in

                  let havoc_stmt = Stmt.mk_havoc ~loc pred_heap2_qual_ident in

                  let assume_stmt =
                    let in_vars_eq_args =
                      Expr.mk_eq in_vars_tuple actual_arg_in_exprs_subst_tuple
                      (* List.map2_exn in_vars actual_arg_in_exprs_subst ~f:(fun var_decl arg ->
                           Expr.mk_eq (Expr.from_var_decl var_decl) arg
                         ) *)
                    in

                    let new_chunk =
                      let new_chunk_expr_list =
                        match c.call_decl.call_decl_kind with
                        | Pred ->
                            [
                              Expr.mk_int 1;
                              Expr.mk_tuple actual_arg_out_exprs_subst;
                            ]
                        | Invariant ->
                            [ Expr.mk_tuple actual_arg_out_exprs_subst ]
                        | _ ->
                            Error.error loc
                              "Internal error: Expected a predicate or \
                               invariant"
                      in

                      Expr.mk_app ~loc ~typ:heap_elem_type
                        (Expr.DataConstr pred_ra_constr) new_chunk_expr_list
                    in

                    Stmt.mk_assume_expr ~loc
                      ~cmnt:
                        ((match cmnt with None -> "" | Some cmnt -> cmnt)
                        ^ "\nexhale: "
                        ^ Stdlib.Format.asprintf "%a" Expr.pr
                            (Expr.mk_binder Forall univ_vars_list
                              (Expr.mk_impl (Expr.mk_and conds) expr)))
                      (Expr.mk_binder
                         ~trigs:
                           [
                             [
                               Expr.mk_maplookup ~loc pred_heap2_expr
                                 in_vars_tuple;
                             ];
                             [
                               Expr.mk_maplookup ~loc pred_heap_expr
                                 in_vars_tuple;
                             ];
                           ]
                         ~loc ~typ:Type.bool Forall in_vars
                         (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                            [
                              (* m1(a,b,c) && l == f1(a, b, c) *)
                              Expr.mk_and ~loc (in_vars_eq_args :: conds_subst);
                              (* pred$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                              Expr.mk_eq ~loc
                                (Expr.mk_maplookup ~loc pred_heap2_expr
                                   actual_arg_in_exprs_subst_tuple)
                                (Expr.mk_app ~loc ~typ:heap_elem_type
                                   (Expr.Var pred_heapchunk_operator)
                                   [
                                     Expr.mk_maplookup ~loc pred_heap_expr
                                       in_vars_tuple;
                                     new_chunk;
                                   ]);
                              (* pred$Heap2[l] == pred$Heap[l] *)
                              Expr.mk_eq ~loc
                                (Expr.mk_maplookup ~loc pred_heap2_expr
                                   in_vars_tuple)
                                (Expr.mk_maplookup ~loc pred_heap_expr
                                   in_vars_tuple);
                            ]))
                  in

                  (* pred$Heap := pred$Heap2 *)
                  let eq_stmt =
                    Stmt.mk_assign ~loc [ pred_heap_expr ] pred_heap2_expr
                  in

                  let assert_heap_valid =
                    Stmt.mk_assert_expr ~loc
                      ~spec_error:
                        (Stmt.mk_const_spec_error
                           (Error.RelatedLoc, loc, "This predicate may not hold")
                        :: spec_error)
                      (Expr.mk_app ~loc ~typ:Type.bool
                         (Expr.Var pred_heap_valid_fn) [ pred_heap_expr ])
                  in

                  let* injectivity_assertion =
                    generate_injectivity_assertions ~loc universal_quants conds
                      (Expr.mk_tuple actual_arg_in_exprs)
                  in

                  let stmts_list =
                    match univ_quants_list with
                    | [] -> []
                    | _ -> [ injectivity_assertion ]
                  in

                  let stmts_list =
                    stmts_list
                    @ [ havoc_stmt; assume_stmt; forward_trigger_assertion; eq_stmt; assert_heap_valid ]
                  in

                  let stmt = Stmt.mk_block_stmt ~loc stmts_list in

                  Rewriter.return stmt
              | _ -> Error.error loc "Expected a predicate definition")
          | _ -> unsupported_expr_error expr)
end

let rec rewrite_make_heaps_explicit (s : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match s.stmt_desc with
  | Stmt.Basic basic_stmt -> (
      match basic_stmt with
      | Spec (spec_kind, spec) -> (
          match spec_kind with
          | Inhale ->
              let expr = spec.spec_form in

              let* stmt =
                TrnslInhale.trnsl_inhale_expr ?cmnt:spec.spec_comment
                  ~spec_error:spec.spec_error ~loc:s.stmt_loc expr
              in
              Rewriter.return stmt
          | Exhale ->
              let expr = spec.spec_form in

              let* stmt =
                TrnslExhale.trnsl_exhale_expr ?cmnt:spec.spec_comment
                  ~spec_error:spec.spec_error ~loc:s.stmt_loc expr
              in
              Rewriter.return stmt
          | Assume ->
              let expr = spec.spec_form in

              let* stmt =
                TrnslInhale.trnsl_assume_expr ?cmnt:spec.spec_comment
                  ~spec_error:spec.spec_error ~loc:s.stmt_loc expr
              in
              Rewriter.return stmt
          | Assert ->
              let* is_e_pure = Rewriter.ProgUtils.is_expr_pure spec.spec_form in
              if is_e_pure then
                (* let assume_stmt = Stmt.mk_assume_expr ~loc:s.stmt_loc spec.spec_form in *)
                (* Rewriter.return (Stmt.mk_block_stmt ~loc:s.stmt_loc [s; assume_stmt]) *)
                (* The corresponding assume stmt is being added in backend/checker.ml *)
                Rewriter.return s
              else
                let loc = Stmt.to_loc s in
                let nondet_var =
                  Type.
                    {
                      var_name = Ident.fresh loc "$nondet";
                      var_loc = loc;
                      var_type = Type.bool;
                      var_const = true;
                      var_ghost = false;
                      var_implicit = false;
                    }
                in

                let (nondet_var_def : Module.symbol) =
                  VarDef { var_decl = nondet_var; var_init = None }
                in

                let* _ = Rewriter.introduce_symbol nondet_var_def in

                let* exhale_stmt =
                  TrnslExhale.trnsl_exhale_expr
                    ?cmnt:
                      (Some
                         (Option.value ~default:(Stmt.to_string s)
                            spec.spec_comment))
                    ~spec_error:spec.spec_error ~loc spec.spec_form
                in
                let assume_false_stmt =
                  Stmt.mk_assume_expr ~loc (Expr.mk_bool false)
                in

                let cond_stmt =
                  Stmt.Cond
                    {
                      cond_test = Some (Expr.from_var_decl nondet_var);
                      cond_then =
                        Stmt.mk_block_stmt ~loc
                          [ exhale_stmt; assume_false_stmt ];
                      cond_else = Stmt.mk_block_stmt ~loc [];
                      cond_if_assumes_false = true;
                    }
                in

                let nondet_false_stmt =
                  Stmt.mk_assume_expr ~loc
                    (Expr.mk_not (Expr.from_var_decl nondet_var))
                in

                let* assume_stmt =
                  TrnslInhale.trnsl_assume_expr ?cmnt:spec.spec_comment
                    ~spec_error:spec.spec_error ~loc:s.stmt_loc spec.spec_form
                in

                let new_stmt =
                  Stmt.mk_block_stmt ~loc
                    [
                      Stmt.{ stmt_desc = cond_stmt; stmt_loc = loc };
                      nondet_false_stmt;
                      assume_stmt;
                    ]
                in

                Rewriter.return new_stmt)
      | FieldRead fr_desc ->
          let* lhs_var =
            Rewriter.find_and_reify s.stmt_loc fr_desc.field_read_lhs
          in
          let lhs_var =
            match lhs_var with
            | VarDef var_symbol -> var_symbol.var_decl
            | _ -> Error.type_error s.stmt_loc "Expected a variable definition."
          in

          let field_name = fr_desc.field_read_field in
          let field_loc = fr_desc.field_read_field |> QualIdent.to_loc in
          let* field_symbol = Rewriter.find_and_reify s.stmt_loc field_name in

          let field_symbol =
            match field_symbol with
            | FieldDef field_symbol -> field_symbol
            | _ -> Error.type_error field_loc "Expected a field definition."
          in

          let field_ra =
            Rewriter.ProgUtils.field_get_ra_qual_iden field_symbol
          in
          let field_read_ref_loc = fr_desc.field_read_ref |> Expr.to_loc in
          let loc = Loc.merge field_loc field_read_ref_loc in
          
          let* orig_ra_name, ra_def, _ = Rewriter.find s.stmt_loc field_ra in

          if QualIdent.(orig_ra_name = Predefs.lib_frac_mod_qual_ident) then
            let field_ra_type = Rewriter.ProgUtils.get_ra_rep_type field_ra in

            let field_heap_name = field_heap_name field_name in
            let field_heap_expr =
              Expr.mk_var
                ~typ:(Type.mk_map s.stmt_loc Type.ref field_ra_type)
                (QualIdent.from_ident field_heap_name)
            in

            let field_val_destr =
              QualIdent.append field_ra Predefs.lib_frac_chunk_destr1_ident
            in
            let field_frac_destr =
              QualIdent.append field_ra Predefs.lib_frac_chunk_destr2_ident
            in

            let assert_expr =
              Expr.mk_app ~loc:s.stmt_loc ~typ:Type.bool Expr.Gt
                [
                  Expr.mk_app ~typ:Type.real (DataDestr field_frac_destr)
                    [ Expr.mk_maplookup field_heap_expr fr_desc.field_read_ref ];
                  Expr.mk_real 0.;
                ]
            in

            let assert_stmt =
              let error =
                ( Error.Verification,
                  loc,
                  "Could not assert sufficient permissions to access this field"
                )
              in
              Stmt.mk_assert_expr ~loc:s.stmt_loc
                ~spec_error:[ Stmt.mk_const_spec_error error ]
                assert_expr
            in

            let assign_stmt =
              Stmt.mk_assign ~loc:s.stmt_loc
                [ Expr.from_var_decl lhs_var ]
                (Expr.mk_app ~typ:lhs_var.var_type (DataDestr field_val_destr)
                   [ Expr.mk_maplookup field_heap_expr fr_desc.field_read_ref ])
            in

            Rewriter.return
              (Stmt.mk_block_stmt ~loc:s.stmt_loc [ assert_stmt; assign_stmt ])
          else Error.type_error s.stmt_loc "Expected a FracRA type."
      | Assign
          {
            assign_lhs = [ Expr.App (Read, [ ref_expr; field_expr ], _) ];
            assign_rhs;
            _;
          } ->
          let field_name = Expr.to_qual_ident field_expr in

          let* field_symbol = Rewriter.find_and_reify s.stmt_loc field_name in

          let field_symbol =
            match field_symbol with
            | FieldDef field_symbol -> field_symbol
            | _ -> Error.type_error s.stmt_loc "Expected a field definition."
          in

          let field_ra =
            Rewriter.ProgUtils.field_get_ra_qual_iden field_symbol
          in

          let* orig_ra_name, ra_def, _ = Rewriter.find s.stmt_loc field_ra in

          if QualIdent.(orig_ra_name = Predefs.lib_frac_mod_qual_ident) then
            let field_ra_type = Rewriter.ProgUtils.get_ra_rep_type field_ra in

            let field_heap_name = field_heap_name field_name in
            let field_heap_expr =
              Expr.mk_var
                ~typ:(Type.mk_map s.stmt_loc Type.ref field_ra_type)
                (QualIdent.from_ident field_heap_name)
            in

            let field_frac_destr =
              QualIdent.append field_ra Predefs.lib_frac_chunk_destr2_ident
            in
            let field_frac_constr =
              QualIdent.append field_ra Predefs.lib_frac_chunk_constr_ident
            in

            let assert_expr =
              Expr.mk_app ~loc:s.stmt_loc ~typ:Type.bool Expr.Geq
                [
                  Expr.mk_app ~typ:Type.real (DataDestr field_frac_destr)
                    [ Expr.mk_maplookup field_heap_expr ref_expr ];
                  Expr.mk_real 1.;
                ]
            in

            let new_val =
              Expr.mk_app ~typ:field_ra_type (DataConstr field_frac_constr)
                [ assign_rhs; Expr.mk_real 1. ]
            in

            let assert_stmt =
              let error =
                ( Error.Verification,
                  s.stmt_loc,
                  "Could not assert sufficient permissions to assign this field"
                )
              in
              Stmt.mk_assert_expr ~loc:s.stmt_loc
                ~spec_error:[ Stmt.mk_const_spec_error error ]
                assert_expr
            in
            let assign_stmt =
              Stmt.mk_assign ~loc:s.stmt_loc [ field_heap_expr ]
                (Expr.mk_app
                   ~typ:(Type.mk_map s.stmt_loc Type.ref field_ra_type)
                   MapUpdate
                   [ field_heap_expr; ref_expr; new_val ])
            in

            Rewriter.return
              (Stmt.mk_block_stmt ~loc:s.stmt_loc [ assert_stmt; assign_stmt ])
          else Error.type_error s.stmt_loc "Expected a FracRA type."
      | _ -> Rewriter.return s)
  | _ ->
      let* s = Rewriter.Stmt.descend s ~f:rewrite_make_heaps_explicit in

      Rewriter.return s
