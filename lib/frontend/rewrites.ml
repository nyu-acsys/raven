open Base
open Ast

let rec collect_vars (expr: expr) : expr list =
  match expr with
  | App (constr, expr_list, _) ->
    let init_list =
      match constr with
      | Var _ -> [expr] 
      | _ -> []
    in

    List.fold (List.map expr_list ~f:collect_vars) ~init:init_list ~f:(List.append)

  | Binder (_, v_l, expr, _) ->
    let var_expr_list = collect_vars expr in

    List.filter var_expr_list ~f:(fun var ->
      List.fold v_l ~init:false ~f:(fun b var_decl ->
        b || (QualIdent.equal (QualIdent.from_ident var_decl.var_name) (Expr.to_qual_ident var))
      )
    )

let rec rewrite_compr_expr (expr: expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | Binder (Compr, v_l, inner_expr, _expr_attr) ->
    let* _ = Rewriter.add_locals v_l
    and* inner_expr = rewrite_compr_expr inner_expr in
        
    let compr_fn_ident = Ident.fresh (Expr.to_loc expr) "compr" in

    let free_var_exprs = collect_vars inner_expr in
    
    let formal_var_decls = List.map free_var_exprs ~f:(fun var ->
        { Type.var_name = Ident.fresh (Expr.to_loc inner_expr) "tmp";
          var_loc = Expr.to_loc inner_expr;
          var_type = Expr.to_type var;
          var_const = false;
          var_ghost = false;
          var_implicit = false;
        }
      )
    in

    let ret_var_decl = 
      { Type.var_name = Ident.fresh (Expr.to_loc expr) "ret";
        var_loc = Expr.to_loc expr;
        var_type = Expr.to_type expr;
        var_const = false;
        var_ghost = false;
        var_implicit = false;
      } 
    in

    let ret_typ = (Expr.to_type expr) in
    
    let postcond = 
      let spec_form =
        if Type.is_set ret_typ then
          
          let var_decl = List.hd_exn v_l in
          
          Expr.mk_binder ~typ:Type.bool Forall [var_decl] (
            Expr.mk_app ~typ:Type.bool Impl [
              inner_expr;
              
              Expr.mk_app ~typ:Type.bool Elem [ 
                Expr.from_var_decl var_decl;
                Expr.from_var_decl ret_var_decl
              ]
            ]
          )
            
        else 
          (* Type.is_map ret_typ *)
          let var_decl = List.hd_exn v_l in
          
          Expr.mk_binder ~typ:Type.bool Forall [var_decl] 
            (Expr.mk_app ~typ:Type.bool Eq
               [ inner_expr;
                 
                 Expr.mk_app ~typ:(Type.map_codom ret_typ) MapLookUp [ 
                   Expr.from_var_decl ret_var_decl;
                   Expr.from_var_decl var_decl ]
               ]
            )

      in
      
      { Stmt.spec_form = spec_form;
        spec_atomic = false;
        spec_error = None;
      } 
      
    in

    let call_decl = {
      Callable.call_decl_kind = Func;
      call_decl_name = compr_fn_ident;
      call_decl_formals = formal_var_decls;
      call_decl_returns = [ret_var_decl];
      call_decl_locals = [];
      call_decl_precond = [];
      call_decl_postcond = [postcond];
      call_decl_loc = Expr.to_loc expr;
    } 
      
    in

    let compr_fn_qual_ident = QualIdent.from_ident compr_fn_ident in
    let compr_fn_def = Module.CallDef (Callable.{ call_decl; call_def = FuncDef { func_body = None;} }) in
    
    let new_expr = 
      Expr.mk_app ~typ:(ret_typ) ~loc:(Expr.to_loc expr) (Expr.Var compr_fn_qual_ident) free_var_exprs
    in

    let+ _ = Rewriter.introduce_symbol compr_fn_def in
    new_expr
      
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_compr_expr

let rewrite_compr_modules (tbl: SymbolTbl.t) (m: Module.t) =
  Rewriter.eval (Rewriter.Module.rewrite_expressions ~f:rewrite_compr_expr m) tbl
