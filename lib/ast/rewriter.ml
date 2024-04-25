open Base
open AstDef
open Util

(* type state = { *)
type 'a state = {
  state_table: SymbolTbl.t;
  state_update_table: bool;
  state_new_symbols: Module.symbol list list;
  state_user_data: 'a;
}

type ('a, 'b) t_ext = 'b state -> ('b state * 'a)
type 'a t = ('a, unit) t_ext

(* type 'a t = state -> (state * 'a) *)

let return a = fun s -> (s, a)

module Syntax = struct
  (* For ppx_let *)
  module Let_syntax = struct 
    let bind m ~f = fun sin ->
      let sout, res = m sin in
      f res sout
    [@@inline always]

    let return = return

    let map m ~f = fun sin ->
      let sout, res = m sin in
      (sout, f res)
    [@@inline always]
      
    let both m1 m2 = fun sin ->
      let s1, res1 = m1 sin in
      let s2, res2 = m2 s1 in
      (s2, (res1, res2))
    [@@inline always]
  end
    
  open Let_syntax
  
  let (let+) (m: 'c state -> 'c state * 'a) (f: 'a -> 'b) : ('c state -> 'c state * 'b) = map m ~f [@@inline always]
  let (and+) = both
  let (let* ) (m: 'c state -> 'c state * 'a) (f: 'a -> 'c state -> 'c state * 'b) : ('c state -> 'c state * 'b) = bind m ~f [@@inline always]
  let (and* ) = both
  
end


let eval ?(update=true) m tbl =
  let sin =
    { state_table = tbl;
      state_update_table = update;
      state_new_symbols = [];
      state_user_data = ();
    }
  in
  let sout, res = m sin in
  (*  *)

  (* Logs.debug (fun m -> m "Rewriter.eval: SymbolTbl Symbols: \n%a\n" (Util.Print.pr_list_comma (fun ppf (k,v) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k Module.pr_symbol v)) (Map.to_alist (Map.filter_keys sout.state_table.tbl_symbols ~f:(fun k -> Poly.((QualIdent.to_string k) = "$Program.pr"))))); *)


  sout.state_table, res


let eval_with_user_state ~init (f:('a state -> 'a state * 'b)) : 'b t =
  fun st -> 
    
    let st, v  = f { st with state_user_data = init } in

    let st = { st with state_user_data = () } in
    st, v

    
let init s _ = s, ()
                             
let get_table s = s, s.state_table

(** Warning: should only be used for debugging purposes *)
let __get_state s = s, s

let current_scope s : 'a state * SymbolTbl.scope = s, s.state_table.tbl_curr

let current_scope_id s : 'a state * qual_ident = s, s.state_table.tbl_curr.scope_id

let current_scope_children s : 'a state * SymbolTbl.scope IdentHashtbl.t = s, s.state_table.tbl_curr.scope_children

let current_scope_entries s : 'a state * SymbolTbl.entry IdentHashtbl.t = s, s.state_table.tbl_curr.scope_entries

let current_user_state s : 'a state * 'a = s, s.state_user_data
let set_user_state user_data s = { s with state_user_data = user_data }, ()

let current_module_name s : 'a state * qual_ident = 
  let s, curr_scope = current_scope s in

  if curr_scope.scope_is_local then
    s, QualIdent.pop curr_scope.scope_id
  else begin
    (* Logs.warn (fun m -> m "Rewrites.generate_inv_function: Expected a local scope, but got a non-local scope: %a" QualIdent.pr curr_scope.scope_id); *)
    s, curr_scope.scope_id
  end
  
  


let update_table f s =
  { s with state_table = f s.state_table },
  ()

let exit_module (mdef: Module.t) s =
  (* Logs.debug (fun m -> m "exit_module: %a" Module.pr (mdef)); *)

  let tbl = s.state_table in
  let new_symbols, mdef = 
    match s.state_new_symbols with
    | symbols :: new_symbols ->
      (* Logs.debug (fun m -> m "exit_module: %a;\nnew symbols: %a" Ident.pr (mdef.mod_decl.mod_decl_name) (Print.pr_list_comma AstDef.Symbol.pr) symbols); *)

      let open Module in
      let new_instr = List.rev_map ~f:(fun def -> SymbolDef def) symbols in
      new_symbols,      
      { mdef with mod_def = new_instr @ mdef.mod_def }
    | new_symbols -> 
      assert (List.is_empty new_symbols);
      new_symbols, mdef
  in
  { s with
    state_table = SymbolTbl.exit tbl;
    state_new_symbols = new_symbols
  },
  mdef


let exit_callable (call_def: Callable.t) s =
  Logs.debug (fun m -> m "exit_callable: %a" Ident.pr (call_def.call_decl.call_decl_name));
  (* (match call_def.call_def with
   | Callable.FuncDef { func_body = Some _; _ } -> ()
   | Callable.ProcDef { proc_body = Some pp; _ } -> 
    Logs.debug (fun m -> m "exit_callable: proc_body = %a" AstDef.Stmt.pr pp);
   | _ -> ()); *)

  let tbl = s.state_table in
  let new_symbols, call_def =
    match s.state_new_symbols with
    | new_callable_symbols :: new_mod_symbols :: new_symbols ->
      let open Callable in
      (* Logs.debug (fun m -> m "exit_callable: new_callable_symbols = %a" (Print.pr_list_comma AstDef.Symbol.pr) new_callable_symbols); *)
      let new_locals, new_mod_symbols1 =
        List.partition_map new_callable_symbols ~f:(function
            | VarDef ({ var_init = None ; _ } as var_def) -> First var_def.var_decl
            | symbol -> Second symbol)
      in
      let call_decl =
        { call_def.call_decl with
          call_decl_locals = List.rev_append new_locals call_def.call_decl.call_decl_locals
        }
      in
      (* if (List.is_empty new_mod_symbols1) then
        ()
      else
        Logs.debug (fun m -> m "exit_callable: new_mod_symbols = %a" (Print.pr_list_comma AstDef.Symbol.pr) new_mod_symbols1); *)
        
      (new_mod_symbols1 @ new_mod_symbols) :: new_symbols,
      { call_def with call_decl }
    | new_symbols -> 
      Logs.debug (fun m -> m "exit_callable: No New Symbols");
      new_symbols, call_def
  in
  { s with
    state_table = SymbolTbl.exit tbl;
    state_new_symbols = new_symbols
  },
  call_def

let enter symbol s =
  Logs.debug (fun m -> m "Rewriter.enter: symbol = %a" Ident.pr (AstDef.Symbol.to_name symbol));
  (* Logs.debug (fun m -> m "Rewriter.enter: symbol = %a" Symbol.pr (symbol)); *)
  let _ = match symbol with
    | Module.ModDef _ | CallDef _ -> ()
    | _ -> failwith "enter: expected module or callable symbol"
  in
  let symbol_loc = Symbol.to_loc symbol in
  let symbol_ident = Symbol.to_name symbol in
  {
    s with
    state_table = SymbolTbl.enter symbol_loc symbol_ident s.state_table;
    state_new_symbols = [] :: s.state_new_symbols
  },
  ()

let enter_module mdef = enter (ModDef mdef)

let enter_callable callable = 
  Logs.debug (fun m -> m "Rewriter.enter_callable: callable ");
  enter (CallDef callable)

let declare_symbol symbol : unit t = update_table (SymbolTbl.add_symbol symbol)

let introduce_symbol symbol s =
  { s with
    state_table =
      if s.state_update_table
      then SymbolTbl.add_symbol symbol s.state_table
      else s.state_table;
    state_new_symbols = match s.state_new_symbols with
      | scope :: new_symbols -> (symbol :: scope) :: new_symbols
      | _ -> failwith "empty scope"
  },
  ()


let introduce_typecheck_symbol ~loc ~(f: AstDef.Module.symbol -> AstDef.Module.symbol t) (symbol: Module.symbol) (s: 'a state) : 'a state * qual_ident =
  (* f represents a typechecking function that will be used to type-check symbol in once the state has been set in the correct scope. Typically, this function will be the Typing.process_symbol function. However, this cannot be set statically since it will create a recursive dependency between Rewriter and Typing. *)
  
  (* Logs.debug (fun m -> m "Rewriter.introduce_typecheck_symbol: symbol = %a" AstDef.Ident.pr (AstDef.Symbol.to_name symbol)); *)
  Logs.debug (fun m -> m "Rewriter.introduce_typecheck_symbol: symbol = %a" Symbol.pr symbol);
  let current_scope = s.state_table.tbl_curr.scope_id in
  let qual_ident = QualIdent.append current_scope (Symbol.to_name symbol) in

  let (s, _), already_defined = try 
    (declare_symbol symbol s), false 
  with
  | _ -> (s, ()), true
in


  (* if symbol is getting added to parent scope (see appropriate_scope in SymbolTbl.add_symbol, then we need to go to parent scope before calling `f` on `symbol`) *)

  (* let s, symbol = f symbol s in *)
  let (s, symbol), qual_ident = 
    match symbol with
    | VarDef _ -> 
      if not already_defined then
        (f symbol s), qual_ident
      else
        (s, symbol), qual_ident

    | _ ->

      if s.state_table.tbl_curr.scope_is_local then
        let curr_scope_name = s.state_table.tbl_curr.scope_id.qual_base in
        let curr_scope_symbols = (List.hd_exn s.state_new_symbols) in

        let empty_module = Module.{
            mod_decl = empty_decl;
            mod_def = [];
        } (* using empty module to exit. Result of exit_module is thrown away, so it doesn't matter *)
        
        in
        let s, _ = exit_module empty_module s in

        let s, symbol = 
          if not already_defined then
            (f symbol s)
          else
            (s, symbol)
        in

        let qual_ident = QualIdent.append (s.state_table.tbl_curr.scope_id) (Symbol.to_name symbol) in

        let s = { 
          s with
          state_table = SymbolTbl.enter loc curr_scope_name s.state_table;
          state_new_symbols = curr_scope_symbols :: s.state_new_symbols
        } in
        
        (s, symbol), qual_ident
      else
        (f symbol s), qual_ident
  
  in


  
  Logs.debug (fun m -> m "Rewriter.introduce_typecheck_symbol end: symbol = %a" Symbol.pr (symbol));

  { s with
    state_new_symbols =
      match s.state_new_symbols with
      | scope :: new_symbols -> (symbol :: scope) :: new_symbols
      | _ -> failwith "empty scope";
  }, qual_ident

let introduce_toplevel_symbol ~loc ~(f: AstDef.Module.symbol -> AstDef.Module.symbol t) ?(topscope_name=(QualIdent.from_ident Predefs.prog_ident)) (symbol: Module.symbol) (s: 'a state) : 'a state * qual_ident =
  (* This function takes a symbol and adds it to a top-scope, typically $Program. This is achieved by calling exit_module a bunch of times till we are in the right scope in table. Then, calling the f typechecking function on symbol, then *)

  (* f represents a typechecking function that will be used to type-check symbol in once the state has been set in the correct scope. Typically, this function will be the Typing.process_symbol function. However, this cannot be set statically since it will create a recursive dependency between Rewriter and Typing. *)

  Logs.debug (fun m -> m "Rewriter.introduce_toplevel_symbol: topscope_name = %a" QualIdent.pr topscope_name);

  let topscope = SymbolTbl.get_scope_exn topscope_name s.state_table in

  assert (SymbolTbl.is_parent topscope s.state_table);

  let symbol_qual_ident = QualIdent.append topscope_name (Symbol.to_name symbol) in
  match (SymbolTbl.resolve_and_find symbol_qual_ident s.state_table), s.state_update_table with
  | Some _, _ | _, false -> s, symbol_qual_ident
  | None, true -> 

    let (s, scope_new_symbols_list : ('a state * ((ident * (Module.symbol list)) list))) =
      let rec pop_fn (topscope: qual_ident) (s: 'a state) (scope_new_symbols_list: ((ident * (Module.symbol list)) list)) : 'a state * ((ident * (Module.symbol list)) list) = 
        if QualIdent.equal s.state_table.tbl_curr.scope_id topscope then
          s, scope_new_symbols_list
        else
          let curr_scope_name = s.state_table.tbl_curr.scope_id.qual_base in
          let curr_scope_symbols = (List.hd_exn s.state_new_symbols) in
          let scope_new_symbols_list = (curr_scope_name, curr_scope_symbols) :: scope_new_symbols_list in

          let empty_module = Module.{
            mod_decl = empty_decl;
            mod_def = [];
          } (* using empty module to exit. Result of exit_module is thrown away, so it doesn't matter *)
        
          in
          let s, _m = exit_module empty_module s in 

          pop_fn topscope s scope_new_symbols_list
      in

      pop_fn topscope_name s []    
    in

    let s, _ = declare_symbol symbol s in
    let s, symbol = f symbol s in


    let s = { s with
      state_new_symbols =
        match s.state_new_symbols with
        | scope :: new_symbols -> (symbol :: scope) :: new_symbols
        | _ -> failwith "empty scope";
    } 
    (* Above code is implementing some of the functionalities of introduce_symbol manually. The reason introduce_symbol cannot be called directly is because we want to run type-checking on symbol (using the function `f`). For this, the symbol first needs to be added to the symbolTbl, before calling `f` *)
  
    in

    let s = List.fold scope_new_symbols_list ~init:s ~f:(fun s (scope_name, scope_symbols) ->
        { s with
          state_table = SymbolTbl.enter loc scope_name s.state_table;
          state_new_symbols = scope_symbols :: s.state_new_symbols
        }
        (* since we don't have the actual ModDef/CallDef, cannot call Rewriter.enter.
         Instead, manually implementing its functionality using SymbolTbl.enter. *)
      )
    
    in

    s, symbol_qual_ident

let add_locals var_decls s =
  if s.state_update_table
  then 
    (Logs.debug (fun m -> m "Rewriter.add_locals: var_decls = %a" (Print.pr_list_comma AstDef.Ident.pr) (List.map var_decls ~f:(fun (vd: var_decl) -> vd.var_name)));
    update_table (SymbolTbl.add_local_vars var_decls) s)
  else s, ()

let add_call_decl_locals (call_decl : Callable.call_decl) =
  let open Syntax in
  let+ _ =  add_locals call_decl.call_decl_formals
  and+ _ = add_locals call_decl.call_decl_returns
  and+ _ = add_locals call_decl.call_decl_locals in
  ()

let set_symbol symbol s =
  (* Logs.debug (fun m -> m "Rewriter.set_symbol: symbol = %a" AstDef.Ident.pr (AstDef.Symbol.to_name symbol)); *)
  (* Logs.debug (fun m -> m "Rewriter.set_symbol: symbol = %a" Symbol.pr symbol); *)
  if s.state_update_table
  then { s with state_table = SymbolTbl.set_symbol symbol s.state_table }, ()
  else s, ()

let import import_instr s =
  { s with state_table = SymbolTbl.import import_instr s.state_table },
  ()


let wrap_user_state_rewriter (f: 'a state -> 'a state * 'b) (s: unit state) : 'a state * 'b =
  f s

module List = struct

  let map (xs : 'a list) ~(f : 'a -> ('b, 'c) t_ext) : ('b list, 'c) t_ext = fun s ->
    List.fold_map xs ~init:s ~f:(fun s x -> f x s)

  let map2 (xs : 'a list) (ys : 'b list) ~f = fun s ->
    match List.zip xs ys with
    | Ok xs_ys ->
      let s, res = List.fold_map xs_ys ~init:s ~f:(fun s (x, y) -> f x y s) in
      s, Base.List.Or_unequal_lengths.Ok res
    | Unequal_lengths -> s, Unequal_lengths

  let fold_right (xs : 'a list) ~(init : 'b) ~f : ('b, 'c) t_ext = fun s -> 
    List.fold_right xs ~f:(fun x (s, acc) -> f x acc s) ~init:(s, init) 
        
  let fold_left (xs : 'a list) ~(init : 'b) ~f : ('b, 'c) t_ext = fun s ->
    List.fold_left xs ~f:(fun (s, acc) x -> f acc x s) ~init:(s, init)

  let fold_map xs ~init ~f = fun s ->
    let (s, acc), ys = List.fold_map xs ~init:(s, init)
        ~f:(fun (s, acc) x ->
            let s, (acc, y) = f acc x s in
            (s, acc), y)
    in
    s, (acc, ys)
  
  let iter xs ~f = fun s ->
    List.fold_left xs ~init:s ~f:(fun s x -> let res, () = f x s in res), ()

  let exists xs ~f =
    let rec ex xs s =
      match xs with
      | [] -> s, false
      | x :: ys ->
        let s, b = f x s in
        if b then s, b else ex ys s
    in
    ex xs

  let for_all xs ~f =
    let rec ex xs s =
      match xs with
      | [] -> s, true
      | x :: ys ->
        let s, b = f x s in
        if b then ex ys s else s, b
    in
    ex xs
end

module Option = struct

  let map (x: 'a option) ~(f: 'a -> ('b, 'c) t_ext): ('b option, 'c) t_ext = 
    let open Syntax in
    match x with
    | None -> return None
    | Some v ->
      let+ res = f v in
      Some res

end

module VarDecl = struct

  let rewrite_types ~f var_decl : (var_decl, 'a) t_ext =
    let open Syntax in
    let+ var_type = f var_decl.AstDef.Type.var_type in
    { var_decl with var_type = var_type }  
end

module Type = struct
  let descend ~f (tp_expr: Type.t) : (Type.t, 'a) t_ext =
    let open Syntax in
    match tp_expr with
    | App (constr, tp_list, tp_attr) ->
      let+ tp_list = List.map tp_list ~f in
      Type.App (constr, tp_list, tp_attr)

  let rec fold ~(init: 'a) ~(f: 'a -> Type.t -> ('a, 'b) t_ext) tp_expr : ('a, 'b) t_ext =
    let open Syntax in
    match tp_expr with
    | Type.App (_constr, tp_list, _tp_attr) as typ ->
      let* acc = f typ init in
      List.fold_left tp_list ~f:(fun acc typ -> fold ~f ~init:acc typ) ~init:acc
    
  
  let rec rewrite_qual_idents ~f (tp_expr: Type.t) : (Type.t, 'a) t_ext =
    let open Syntax in
    match tp_expr with
    | App (Var id, [], tp_attr) ->
      return (Type.App (Var (f id), [], tp_attr))
    | App (Data (qual_id, variant_decls_list), [], tp_attr) ->
      let qual_id = f qual_id in
      let* variant_decls_list = List.map variant_decls_list ~f:(fun variant_decl ->
        let+ var_decls_list = List.map variant_decl.variant_args ~f:(fun var_decl ->
          VarDecl.rewrite_types ~f:(rewrite_qual_idents ~f) var_decl)
        
        in
        { variant_decl with variant_args = var_decls_list }
        )
      in
      return (Type.App (Data (qual_id, variant_decls_list), [], tp_attr))
    | _ -> descend ~f:(rewrite_qual_idents ~f) tp_expr
  
end



module Expr = struct
  let descend ~f (expr: Expr.t) : (Expr.t, 'a) t_ext =
    let open Syntax in
    match expr with
    | App (constr, expr_list, expr_attr) ->
      let+ expr_list = List.map expr_list ~f in
      Expr.App (constr, expr_list, expr_attr)

    | Binder (b, v_l, trgs, inner_expr, expr_attr) ->
      let+ _ = add_locals v_l
      and+ inner_expr = f inner_expr
      and+ trgs = List.map trgs ~f:(List.map ~f) in
      Expr.Binder (b, v_l, trgs, inner_expr, expr_attr)

  let rec rewrite_types ~(f: AstDef.Type.t -> (AstDef.Type.t, 'a) t_ext) (expr: Expr.t) : (Expr.t, 'a) t_ext =
    let open Syntax in
    match expr with
    | App (constr, expr_list, expr_attr) ->
      let+ expr_list = List.map expr_list ~f:(rewrite_types ~f)
      and+ expr_type = f expr_attr.expr_type in
      let expr_attr = { expr_attr with expr_type = expr_type } in
      Expr.App (constr, expr_list, expr_attr)

    | Binder (b, var_decls, trgs, inner_expr, expr_attr) ->
      let* var_decls = List.map var_decls ~f:(VarDecl.rewrite_types ~f) in
      let+ _ = add_locals var_decls
      and+ inner_expr = rewrite_types ~f inner_expr 
      and+ trgs = List.map trgs ~f:(fun exprs -> List.map exprs ~f:(rewrite_types ~f)) in
      Expr.Binder (b, var_decls, trgs, inner_expr, expr_attr)
    
  let rec rewrite_qual_idents ~f (expr: Expr.t) : (Expr.t, 'a) t_ext =
    let open Syntax in
    match expr with
    | App (constr, expr_list, expr_attr) ->
      let+ expr_list = List.map expr_list ~f:(rewrite_qual_idents ~f)
      and+ expr_type = Type.rewrite_qual_idents ~f expr_attr.expr_type in
      let expr_attr = { expr_attr with expr_type = expr_type } in
      let constr = match constr with
        | Var qual_ident -> Expr.Var (f qual_ident)
        | DataConstr qual_ident -> Expr.DataConstr (f qual_ident)
        | DataDestr qual_ident -> Expr.DataDestr (f qual_ident)
        | _ -> constr
      in
      Expr.App (constr, expr_list, expr_attr)

    | Binder (b, var_decls, trgs, inner_expr, expr_attr) ->
      let* var_decls = List.map var_decls ~f:(VarDecl.rewrite_types ~f:(Type.rewrite_qual_idents ~f)) in
      let+ _ = add_locals var_decls
      and+ inner_expr = rewrite_qual_idents ~f inner_expr 
      and+ trgs = List.map trgs ~f:(fun exprs -> List.map exprs ~f:(rewrite_qual_idents ~f)) in

      Expr.Binder (b, var_decls, trgs, inner_expr, expr_attr)
    
end

module Stmt = struct
  let descend ~(f: Stmt.t -> (Stmt.t, 'a) t_ext) (stmt: Stmt.t) : (Stmt.t, 'a) t_ext =
    let open Syntax in
    match stmt.stmt_desc with
    | Block block_desc ->
      let+ stmt_list = List.map block_desc.block_body ~f in
      { stmt with stmt_desc = Block { block_desc with block_body = stmt_list; } }
    | Loop loop_desc ->
      let+ new_prebody = f loop_desc.loop_prebody 
      and+ new_postbody = f loop_desc.loop_postbody in
      
      let loop_desc =
        { loop_desc with
          loop_prebody = new_prebody;
          loop_postbody = new_postbody;
        }
      in

      { stmt with stmt_desc = Loop loop_desc }

    | Cond cond_desc ->
      let+ new_then_branch = f cond_desc.cond_then
      and+ new_else_branch = f cond_desc.cond_else in
      
      let cond_desc =
        { cond_desc with
          cond_then = new_then_branch;
          cond_else = new_else_branch;
        }
      in
      
      { stmt with stmt_desc = Cond cond_desc }
    | _ -> return stmt
  
  let rewrite_expressions_top ~f ~c (stmt: Stmt.t) : (Stmt.t, 'a) t_ext =
  let open Syntax in
  match stmt.stmt_desc with
  | Basic basic_stmt -> begin
    match basic_stmt with 
    | VarDef var_def ->
      let+ new_init = Option.map var_def.var_init ~f in
      { stmt with stmt_desc = Basic (VarDef { var_def with var_init = new_init; }); }

    | Spec (sk, spec) ->
      let+ new_spec_form = f spec.spec_form in
      { stmt with stmt_desc = Basic (Spec (sk, { spec with spec_form = new_spec_form; })); }

    | Assign assign ->
      let* new_lhs = List.map assign.assign_lhs ~f in
      let+ new_expr = f assign.assign_rhs in
      { stmt with stmt_desc = Basic (Assign { assign_lhs = new_lhs; assign_rhs = new_expr; }); }

    | Bind bind_desc ->
      let* bind_lhs = List.map bind_desc.bind_lhs ~f in
      let+ bind_rhs = f bind_desc.bind_rhs in
      { stmt with stmt_desc = Basic (Bind { bind_lhs; bind_rhs }) }

    | FieldRead field_read_desc ->
      let field_read_lhs = field_read_desc.field_read_lhs in
      let field_read_field = field_read_desc.field_read_field in
      let+ field_read_ref = f field_read_desc.field_read_ref in
      { stmt with stmt_desc = Basic (FieldRead { field_read_lhs; field_read_field; field_read_ref }) }

    | Return expr ->
      let+ expr = f expr in
      { stmt with stmt_desc = Basic (Return expr); }

    | Call call ->
      let+ call_args = List.map call.call_args ~f in
      { stmt with stmt_desc = Basic (Call { call with call_args }) }

    | Use use_desc ->
      let+ use_args = List.map use_desc.use_args ~f in
      { stmt with stmt_desc = Basic (Use { use_desc with use_args }) }
      
    | New new_desc ->
      let+ new_args = List.map new_desc.new_args ~f:(fun (x, e_opt) ->
          let+ e_opt = Option.map e_opt ~f in
          (x, e_opt))
      in
      { stmt with stmt_desc = Basic (New { new_desc with new_args }) }

    | Fpu fpu_desc ->
      let* fpu_old_val = Option.map fpu_desc.fpu_old_val ~f in
      let+ fpu_new_val = f fpu_desc.fpu_new_val in
      { stmt with stmt_desc = Basic (Fpu { fpu_desc with fpu_old_val; fpu_new_val }) }


    (* TODO: add remaining *)
    | _ -> return stmt
    end

  | Loop loop_desc ->
    let+ new_contract = List.map loop_desc.loop_contract ~f:(fun contract ->
        let+ new_spec_form = f contract.spec_form in
        { contract with spec_form = new_spec_form }
      )
    and+ new_prebody = c loop_desc.loop_prebody 
    and+ new_test = f loop_desc.loop_test
    and+ new_postbody = c loop_desc.loop_postbody in
    { stmt with stmt_desc = Loop {
          loop_contract = new_contract;
          loop_prebody = new_prebody;
          loop_test = new_test;
          loop_postbody = new_postbody;
        };
    }

  | Cond cond_desc ->
    let+ new_test = f cond_desc.cond_test
    and+ new_then_branch = c cond_desc.cond_then
    and+ new_else_branch = c cond_desc.cond_else in

    { stmt with stmt_desc = Cond {
          cond_test = new_test;
          cond_then = new_then_branch;
          cond_else = new_else_branch;
        };
    }

  | _ -> descend stmt ~f:c

  let rec rewrite_expressions ~f stmt : (Stmt.t, 'a) t_ext =
    rewrite_expressions_top ~f ~c:(rewrite_expressions ~f) stmt
  
  let rec rewrite_types ~f stmt : (Stmt.t, 'a) t_ext =
    let open Syntax in
    match stmt.Stmt.stmt_desc with
    | Stmt.Basic (VarDef var_def) ->
      let* var_decl = VarDecl.rewrite_types ~f var_def.var_decl
      and* new_init = Option.map var_def.var_init ~f:(Expr.rewrite_types ~f) in
      let+ _ = add_locals [var_decl] in
      { stmt with stmt_desc = Basic (VarDef { var_decl = var_decl; var_init = new_init; }); }
    | _ -> rewrite_expressions_top ~f:(Expr.rewrite_types ~f) ~c:(rewrite_types ~f) stmt

  let rec rewrite_qual_idents ~f stmt : (Stmt.t, 'a) t_ext =
    let open Syntax in
    match stmt.Stmt.stmt_desc with
    | Basic basic_stmt ->
      begin match basic_stmt with
      | VarDef var_def ->
        let+ var_decl = VarDecl.rewrite_types ~f:(Type.rewrite_qual_idents ~f) var_def.var_decl
        and+ var_init = Option.map var_def.var_init ~f:(Expr.rewrite_qual_idents ~f) in        
        { stmt with stmt_desc = Basic (VarDef { var_decl; var_init }); }
                
      | Assign assign ->
        let+ assign_rhs = Expr.rewrite_qual_idents ~f assign.assign_rhs
        and+ assign_lhs = List.map assign.assign_lhs ~f:(Expr.rewrite_qual_idents ~f) in
        { stmt with stmt_desc = Basic (Assign { assign_lhs; assign_rhs }); }

      | Bind bind_desc ->
        let+ bind_lhs = List.map bind_desc.bind_lhs ~f:(Expr.rewrite_qual_idents ~f)
        and+ bind_rhs = Expr.rewrite_qual_idents ~f bind_desc.bind_rhs in
        { stmt with stmt_desc = Basic (Bind { bind_lhs; bind_rhs }) }

      | FieldRead field_read_desc ->
        let field_read_lhs = f field_read_desc.field_read_lhs in
        let field_read_field = f field_read_desc.field_read_field in
        let+ field_read_ref = Expr.rewrite_qual_idents ~f field_read_desc.field_read_ref in
        { stmt with stmt_desc = Basic (FieldRead { field_read_lhs; field_read_field; field_read_ref }) }
        
      | Return expr ->
        let+ expr = Expr.rewrite_qual_idents ~f expr in
        { stmt with stmt_desc = Basic (Return expr); }

      | Call call ->
        let+ call_args = List.map call.call_args ~f:(Expr.rewrite_qual_idents ~f) in
        let call_lhs = Base.List.map call.call_lhs ~f in
        let call_name = f call.call_name in
        { stmt with stmt_desc = Basic (Call { call_lhs; call_name; call_args }) }
    
      | Use use_desc ->
        let use_name = f use_desc.use_name in
        let+ use_args = List.map use_desc.use_args ~f:(Expr.rewrite_qual_idents ~f) in
        { stmt with stmt_desc = Basic (Use { use_desc with use_name; use_args }) }
      
      | New new_desc ->
        let new_lhs = f new_desc.new_lhs in
        let+ new_args = List.map new_desc.new_args ~f:(fun (x, e_opt) ->
            let+ e_opt = Option.map e_opt ~f:(Expr.rewrite_qual_idents ~f) in
            (f x, e_opt))
        in
        { stmt with stmt_desc = Basic (New { new_lhs; new_args }) }

      | Fpu fpu_desc ->
        let fpu_field = f fpu_desc.fpu_field in
        let+ fpu_ref = Expr.rewrite_qual_idents ~f fpu_desc.fpu_ref
        and+ fpu_old_val = Option.map fpu_desc.fpu_old_val ~f:(Expr.rewrite_qual_idents ~f)
        and+ fpu_new_val = Expr.rewrite_qual_idents ~f fpu_desc.fpu_new_val in
        { stmt with stmt_desc = Basic (Fpu { fpu_ref; fpu_field; fpu_old_val; fpu_new_val }) }

      (* TODO: add remaining *)
      | _ -> rewrite_expressions_top ~f:(Expr.rewrite_qual_idents ~f) ~c:(rewrite_qual_idents ~f) stmt
      end

    | _ -> rewrite_expressions_top ~f:(Expr.rewrite_qual_idents ~f) ~c:(rewrite_qual_idents ~f) stmt
end

module Callable = struct

  let rewrite_expressions_top ~(fe:expr -> (expr, 'a) t_ext) ~fs callable : (Callable.t, 'a) t_ext =
    let open Syntax in
    let open AstDef.Stmt in
    let rewrite_specs specs =
      List.map specs ~f:(fun spec ->
          let+ new_spec_form = fe spec.spec_form in
          { spec with spec_form = new_spec_form })
    in
    let call_decl = Callable.to_decl callable in
    let* _ = add_call_decl_locals call_decl
    and* new_preconds = rewrite_specs call_decl.call_decl_precond
    and* new_postconds = rewrite_specs call_decl.call_decl_postcond in
    let call_decl =
      { call_decl with 
        call_decl_precond = new_preconds;
        call_decl_postcond = new_postconds;
      }
    in
    match callable.call_def with
    | Callable.FuncDef { func_body } ->
      let+ func_body = Option.map func_body ~f:fe in
      Callable.{ call_decl; call_def = Callable.FuncDef { func_body } }
        
    | Callable.ProcDef { proc_body } ->
      (* Logs.debug (fun m -> m "Rewriter.Callable.rewrite_expressions_top: old_proc_body = %a" (Print.pr_option AstDef.Stmt.pr) proc_body); *)
      let+ proc_body = Option.map proc_body ~f:fs in
      (* Logs.debug (fun m -> m "Rewriter.Callable.rewrite_expressions_top: new_proc_body = %a" (Print.pr_option AstDef.Stmt.pr) proc_body); *)
      Callable.{ call_decl; call_def = Callable.ProcDef { proc_body } }   

  let rewrite_scoped ~f callable =
    let open Syntax in
    Logs.debug (fun m -> m "Rewriter.Callable.rewrite_scoped: callable = %a" Callable.pr callable);
    (* rewrite_scoped assumes the callable will always be opened BEFORE any Callable.rewrite_ call. 
       This is ensured in all the Module.rewrite_ methods.

       Therefore, no need to call enter_callable or exit_callable here.
    *)
    
    Logs.debug (fun m -> m "Rewriter.Callable.rewrite_scoped: entered callable");
    let* callable = f callable in

    return callable
  
  let rewrite_expressions ~f callable =
    rewrite_scoped ~f:(rewrite_expressions_top ~fe:f ~fs:(Stmt.rewrite_expressions ~f)) callable
  
  let rewrite_types_top ~(ft:type_expr -> type_expr t) ~fe ~fs callable : (Callable.t, 'a) t_ext =
    let open Syntax in
    let call_decl = Callable.to_decl callable in
    let* call_decl_formals = List.map call_decl.call_decl_formals ~f:(VarDecl.rewrite_types ~f:ft)
    and* call_decl_returns = List.map call_decl.call_decl_returns ~f:(VarDecl.rewrite_types ~f:ft)
    and* call_decl_locals = List.map call_decl.call_decl_locals ~f:(VarDecl.rewrite_types ~f:ft) in
    let call_decl =
      { call_decl with
        call_decl_formals;
        call_decl_returns;
        call_decl_locals
      }
    in
    let callable = { callable with call_decl } in
    rewrite_expressions_top ~fe ~fs callable

  let rewrite_types ~f callable =
    rewrite_scoped ~f:(rewrite_types_top ~ft:f ~fe:(Expr.rewrite_types ~f) ~fs:(Stmt.rewrite_types ~f)) callable    

  let rewrite_stmts ~f callable =
    let id_expr_rewriter e = return e in

    rewrite_scoped ~f:(rewrite_expressions_top ~fe:id_expr_rewriter ~fs:f) callable 

  let rewrite_qual_idents ~f callable =
    let open Syntax in
    let* callable = rewrite_scoped
      ~f:(rewrite_types_top
            ~ft:(Type.rewrite_qual_idents ~f)
            ~fe:(Expr.rewrite_qual_idents ~f)
            ~fs:(Stmt.rewrite_qual_idents ~f))
      callable

    in

    let call_decl_masks = Base.Option.map callable.call_decl.call_decl_mask ~f:((Base.Set.map (module QualIdent)) ~f) in
    let callable = { callable with call_decl = { callable.call_decl with call_decl_mask = call_decl_masks } } in
    return callable
end

module Module = struct

  let rec rewrite_symbols ~f (mdef: Module.t) : (Module.t, 'a) t_ext =
    let open Module in
    let open Syntax in
    let* _ = enter_module mdef
    and* symbols = List.map mdef.mod_def ~f:(function
        | SymbolDef symbol ->
            (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_symbols: old_symbol: %a" AstDef.Symbol.pr symbol); *)
            let* symbol = f symbol in
            let* _ = set_symbol symbol in
            (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_symbols: new_symbol: %a" AstDef.Symbol.pr symbol); *)

            let* tbl = get_table in
            (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_symbols: SymbolTbl Symbols: \n%a\n" (Util.Print.pr_list_comma (fun ppf (k,v) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k Module.pr_symbol v)) (Map.to_alist (Map.filter_keys tbl.tbl_symbols ~f:(fun k -> Poly.((QualIdent.to_string k) = "$Program.pr"))))); *)

            return (SymbolDef symbol)
        | import -> return import 
      )
    in
    let mdef = { mdef with mod_def = symbols } in
    exit_module mdef

  let rec rec_rewrite_symbols ~f (mdef: Module.t) : (Module.t, 'a) t_ext =
    let open Module in
    let open Syntax in
    let* _ = enter_module mdef
    and* symbols = List.map mdef.mod_def ~f:(function
        | SymbolDef symbol ->
          let* symbol = 
            (match symbol with
            | ModDef mod_def ->
              let* new_mod_def = rec_rewrite_symbols ~f mod_def in
              return @@ ModDef new_mod_def 
            | _ -> return symbol
            ) 
          in

            (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_symbols: old_symbol: %a" AstDef.Symbol.pr symbol); *)
          let+ symbol = f symbol
          and+ _ = set_symbol symbol in
            (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_symbols: new_symbol: %a" AstDef.Symbol.pr symbol); *)
          SymbolDef symbol
        | import -> return import 
      )
    in
    let mdef = { mdef with mod_def = symbols } in
    exit_module mdef
    
  let rec rewrite_expressions ~f mdef : (Module.t, 'a) t_ext =
    let open Syntax in
    let open Module in
    let rewrite_symbol = function
      | VarDef var_def ->
        let+ new_var_init = Option.map var_def.var_init ~f in
        VarDef { var_def with var_init = new_var_init }
      | CallDef call_def ->
        let* _ = enter_callable call_def in

        let* new_call_def = Callable.rewrite_expressions ~f call_def in
        let+ new_call_def = exit_callable new_call_def in

        CallDef new_call_def
      | ModDef mod_def ->
        let+ new_mod_def = rewrite_expressions ~f mod_def in
        ModDef new_mod_def
      | mem_def -> return mem_def
    in
    rewrite_symbols ~f:rewrite_symbol mdef

  let rec rewrite_stmts ~f mdef : (Module.t, 'a) t_ext = 
    let open Syntax in
    let open Module in
    let rewrite_symbol = function
      | CallDef call_def ->
        let* _ = enter_callable call_def in

        let* new_call_def = Callable.rewrite_stmts ~f call_def in
        let+ new_call_def = exit_callable new_call_def in

        CallDef new_call_def
      | ModDef mod_def ->
        let+ new_mod_def = rewrite_stmts ~f mod_def in
        ModDef new_mod_def
      | mem_def -> return mem_def
    in
    rewrite_symbols ~f:rewrite_symbol mdef

  let rec rewrite_types ~f mdef : (Module.t, 'a) t_ext =
    let open Syntax in
    let rewrite_symbol : Module.symbol -> Module.symbol t =
      let open Module in
      function
      | TypeDef type_def ->
        let+ type_def_expr = Option.map type_def.type_def_expr ~f in
        TypeDef { type_def with type_def_expr }
      | ConstrDef constr_def ->
        let+ constr_args = List.map constr_def.constr_args ~f:(VarDecl.rewrite_types ~f)
        and+ constr_return_type = f constr_def.constr_return_type in
        ConstrDef { constr_def with constr_args; constr_return_type }
      | DestrDef destr_def ->
        let+ destr_arg = f destr_def.destr_arg
        and+ destr_return_type = f destr_def.destr_return_type in
        DestrDef { destr_def with destr_arg; destr_return_type }        
      | VarDef var_def ->
        let+ var_decl = VarDecl.rewrite_types ~f var_def.var_decl
        and+ var_init = Option.map var_def.var_init ~f:(Expr.rewrite_types ~f) in
        VarDef { var_decl; var_init }
      | FieldDef field_def ->
        let+ field_type = f field_def.field_type in
        FieldDef { field_def with field_type }
      | CallDef call_def ->
        let* _ = enter_callable call_def in

        let* new_call_def = Callable.rewrite_types ~f call_def in
        let+ new_call_def = exit_callable new_call_def in
        
        CallDef new_call_def

      | ModDef mod_def ->
        let+ new_mod_def = rewrite_types ~f mod_def in
        ModDef new_mod_def
        
      | mem_def -> return mem_def
    in
    rewrite_symbols ~f:rewrite_symbol mdef

  let rec rewrite_callables ~f mdef : (Module.t, 'a) t_ext =
    let open Syntax in
    let rewrite_symbol = 
      let open Module in
      function
      | CallDef call_def ->
        let* _ = enter_callable call_def in

        let* new_call_def = f call_def in
        let+ new_call_def = exit_callable new_call_def in
        (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_callables: new_call_def = %a" AstDef.Callable.pr new_call_def); *)
        CallDef new_call_def
      | ModDef mod_def ->
        let+ new_mod_def = rewrite_callables ~f mod_def in
        (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_callables: new_module_def = %a" AstDef.Module.pr new_mod_def); *)

        ModDef new_mod_def
      | mem_def -> return mem_def
    in
    rewrite_symbols ~f:rewrite_symbol mdef

  let rec rewrite_qual_idents_in_symbol ~(f: QualIdent.t -> QualIdent.t) : Module.symbol -> (Module.symbol, 'a) t_ext =
    let open Syntax in
    let open Module in
    function
      | ModInst mod_inst ->
        let mod_inst_def = Base.Option.map mod_inst.mod_inst_def ~f:(fun (mod_inst_def_funct, mod_inst_def_args) ->
            f mod_inst_def_funct, Base.List.map ~f mod_inst_def_args)
        in
        let mod_inst_type = f mod_inst.mod_inst_type in
        return @@ ModInst { mod_inst with mod_inst_type; mod_inst_def }
      | TypeDef type_def ->
        let+ type_def_expr = Option.map type_def.type_def_expr  ~f:(Type.rewrite_qual_idents ~f) in
        TypeDef { type_def with type_def_expr }
      | ConstrDef constr_def ->
        let+ constr_args = List.map constr_def.constr_args ~f:(VarDecl.rewrite_types ~f:(Type.rewrite_qual_idents ~f))
        and+ constr_return_type = Type.rewrite_qual_idents ~f constr_def.constr_return_type in
        ConstrDef { constr_def with constr_args; constr_return_type }
      | DestrDef destr_def ->
        let+ destr_arg = Type.rewrite_qual_idents ~f destr_def.destr_arg
        and+ destr_return_type = Type.rewrite_qual_idents ~f destr_def.destr_return_type in
        DestrDef { destr_def with destr_arg; destr_return_type }        
      | VarDef var_def ->
        let+ var_decl = VarDecl.rewrite_types ~f:(Type.rewrite_qual_idents ~f) var_def.var_decl
        and+ var_init = Option.map var_def.var_init ~f:(Expr.rewrite_qual_idents ~f) in
        VarDef { var_decl; var_init }
      | FieldDef field_def ->
        let+ field_type = Type.rewrite_qual_idents ~f field_def.field_type in
        FieldDef { field_def with field_type }
      | CallDef call_def ->
        let* _ = enter_callable call_def in

        let* new_call_def = Callable.rewrite_qual_idents ~f call_def in
        let+ new_call_def = exit_callable new_call_def in

        CallDef new_call_def
      | ModDef mod_def ->
        let+ new_mod_def = rewrite_qual_idents ~f mod_def in
        ModDef new_mod_def

  and rewrite_qual_idents ~f mdef : (Module.t, 'a) t_ext =
    (* TODO: rewrite imports *)
    let open Syntax in
    let open Module in
    let+ mdef1 = rewrite_symbols ~f:(rewrite_qual_idents_in_symbol ~f) mdef in
    let mod_decl_interfaces =
      Set.fold mdef1.mod_decl.mod_decl_interfaces ~init:(Set.empty (module QualIdent))
        ~f:(fun interfaces id -> Set.add interfaces (f id))
    in
    let mod_decl_returns = Base.Option.map ~f mdef1.mod_decl.mod_decl_returns in
    let mod_decl =
      { mdef1.mod_decl with
        mod_decl_interfaces;
        mod_decl_returns
      }
    in
    { mdef1 with mod_decl }
end

module Symbol = struct
  let reify (name, symbol, subst) =
    Logs.debug (fun m -> m "Rewriter.Symbol.reify %a; %a" AstDef.Symbol.pr symbol (Print.pr_list_comma (fun ppf (q, i_l) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr q (Print.pr_list_comma Ident.pr) i_l )) subst);

    match subst with
    | [] -> return symbol
    | _ ->
      let open Syntax in
      let+ tbl = get_table in
      let tbl_scope = SymbolTbl.goto (AstDef.Symbol.to_loc symbol) name tbl in
      let _, symbol1 = eval (Module.rewrite_qual_idents_in_symbol ~f:(QualIdent.requalify subst) symbol) tbl_scope in

      (* Logs.debug (fun m -> m "Rewriter.Symbol.reify: Reified symbol = %a" AstDef.Symbol.pr symbol1); *)
      symbol1

  let reify_type_def loc (_name, symbol, subst) : (AstDef.Type.t Base.Option.t, 'a) t_ext =
    let open Syntax in
    match symbol with
    | AstDef.Module.TypeDef { type_def_expr = None; _ } ->
      return None
    | TypeDef { type_def_expr = Some tp_expr; _ } -> 
      let+ tp_expr = Type.rewrite_qual_idents ~f:(QualIdent.requalify subst) tp_expr in
      Some tp_expr
    | _ -> Error.error loc "Expected type identifier"

  let reify_type loc (_name, symbol, subst) : (AstDef.Type.t, 'a) t_ext =
    let tp_expr =
      match symbol with
      | AstDef.Module.VarDef { var_decl; _ } -> var_decl.var_type
      | FieldDef field_def -> field_def.field_type
      | _ -> Error.error loc "Expected expression identifier"
    in
    Type.rewrite_qual_idents ~f:(QualIdent.requalify subst) tp_expr
      
  let reify_field_type loc (_name, symbol, subst) : (AstDef.Type.t, 'a) t_ext =
    let tp_expr =
      match symbol with
      | AstDef.Module.FieldDef { field_type = App(Fld, [tp], _); _ } -> tp
      | _ -> Error.error loc "Expected field identifier"
    in
    Type.rewrite_qual_idents ~f:(QualIdent.requalify subst) tp_expr
  
  let orig_symbol (_name, symbol, _subst) = symbol

  let extract (_name, symbol, subst) ~f =
    f (QualIdent.requalify subst) symbol

  let add_subst s (name, symbol, subst) = (name, symbol, s :: subst)
  
  type t = QualIdent.t * AstDef.Module.symbol * QualIdent.subst
                                 
end

let resolve_and_find loc name : ((QualIdent.t * Symbol.t), 'a) t_ext =
  let open Syntax in
  let+ tbl = get_table in
  (* Logs.debug (fun m -> m "Rewriter.resolve_and_find: tbl_curr: %a" QualIdent.pr (tbl.tbl_curr.scope_id)); *)
  (* Logs.debug (fun m -> m "Rewriter.resolve_and_find: tbl_scope_children: %a" (Print.pr_list_comma Ident.pr) (Hashtbl.keys tbl.tbl_curr.scope_children)); *)
  let alias_qual_ident, qual_ident, symbol, subst = SymbolTbl.resolve_and_find_exn loc name tbl in
  qual_ident, (alias_qual_ident, symbol, subst)

let resolve loc name : (QualIdent.t, 'a) t_ext =
  let open Syntax in
  let+ qual_ident, _ = resolve_and_find loc name in
  Logs.debug (fun m -> m "Rewriter.resolve: name = %a; qual_ident = %a" QualIdent.pr name QualIdent.pr qual_ident);
  qual_ident


let find loc name : (Symbol.t, 'a) t_ext =
  let open Syntax in
  let+ _, symbol = resolve_and_find loc name in
  symbol

let find_and_reify loc name : (AstDef.Module.symbol, 'a) t_ext =
  let open Syntax in
   let* symbol = find loc name in
   Symbol.reify symbol

let is_local loc qual_ident s =
  let s, qual_ident = resolve loc qual_ident s in

  Logs.debug (fun m -> m "Rewriter.is_local: qual_ident = %a" QualIdent.pr qual_ident);
  s, Base.List.is_empty qual_ident.qual_path

module ProgUtils = struct
  let serialize (s: string) : string =
    let s = String.map s ~f:(function
        | '.' -> '_'
        | '[' -> '-'
        | ']' -> '-'
        | '(' -> '*'
        | ')' -> '*'
        | ' ' -> '_'
        | c -> c)
    in
    s

  let field_type_to_frac_mod_ident ~loc field_tp = Ident.make loc (serialize ("Frac$" ^ AstDef.Type.to_string field_tp)) 0

  let pred_to_ra_mod_ident ~loc pred_ident = Ident.make loc (serialize ("PredHeapRA$" ^ (Ident.to_string pred_ident))) 0

  let au_to_ra_mod_ident ~loc call_ident = Ident.make loc (serialize ("AtomicProcHeapRA$" ^ (Ident.to_string call_ident))) 0

  let callable_au_token_ident ~loc callable_ident = Ident.make loc (serialize ("au_token$" ^ (Ident.to_string callable_ident))) 0

  let find_highest_valid_scope_qi loc (qi: qual_ident) : qual_ident t =
    
    let open Syntax in
    Logs.debug (fun m -> m "Rewriter.ProgUtils.find_highest_valid_scope_qi: qi = %a" AstDef.QualIdent.pr qi);
    let rec find_highest_valid_scope_qi' (qi: qual_ident) : qual_ident t =
      (* starting from the current scope, keeps going up till it reaches an abstract scope. Not ideal, since it does not take into account the actual qual_ident `qi` being looked up. *)
      match qi.qual_path with
      | [] -> return (QualIdent.from_ident AstDef.Predefs.prog_ident)
      | _ ->
        let* current_scope = current_scope in
        if current_scope.scope_is_abstract then
          return current_scope.scope_id
        else
          find_highest_valid_scope_qi' (QualIdent.pop current_scope.scope_id)

        (* let* tbl = get_table in
        let scope = SymbolTbl.get_scope_exn (QualIdent.pop qi) tbl in

        if scope.scope_is_abstract then
          return (QualIdent.pop qi)
        else
          find_highest_valid_scope_qi' (QualIdent.pop qi) *)

        (* let* symbol = find_and_reify loc (QualIdent.pop qi) in
        match symbol with
        | ModDef m -> 
          (* Logs.debug (fun mm -> mm "Rewriter.ProgUtils.find_highest_valid_scope_qi: Found module definition = %a" AstDef.Module.pr m);
          if m.mod_decl.mod_decl_is_interface || not (Base.List.is_empty m.mod_decl.mod_decl_formals) then
            return (QualIdent.pop qi)
          else
            find_highest_valid_scope_qi' (QualIdent.pop qi) *)

          let qual_base_is_a_formal = Base.List.fold m.mod_decl.mod_decl_formals ~init:false ~f:(fun acc formal -> acc || Ident.equal formal.mod_inst_name qi.qual_base) in
          (* replace with List.exists *)

          if qual_base_is_a_formal then
            return (QualIdent.pop qi)
          else
            find_highest_valid_scope_qi' (QualIdent.pop qi)
          
        | _ -> Error.error loc "Rewriter.find_highest_valid_scope_qi: Expected module definition." *)

    in

    let* highest_valid_scope = find_highest_valid_scope_qi' qi in

    Logs.debug (fun m -> m "Rewriter.ProgUtils.find_highest_valid_scope_qi: Found scope = %a" AstDef.QualIdent.pr highest_valid_scope);

    return highest_valid_scope

  let find_highest_valid_scope_type_expr loc (tp: type_expr) : (qual_ident option) t =
    let open Syntax in

    (* Logs.debug (fun m -> m "Rewriter.ProgUtils.find_highest_valid_scope_type_expr: tp = %a" AstDef.Type.pr tp); *)
    
    let rec find_highest_valid_scope_type_expr' (tp: type_expr) : (qual_ident list) t =
      match tp with
      | App (constr, tp_expr_list, _) -> 
        let* valid_scopes_list = List.fold_left tp_expr_list ~init:[] ~f:(fun acc tp_expr ->
            let* scopes = find_highest_valid_scope_type_expr' tp_expr in
            return (scopes @ acc)
          )
        in

        let+ valid_scopes_list = 
          match constr with
          | Var qi -> 
            let+ qi_scope = (find_highest_valid_scope_qi loc qi) in
            qi_scope :: valid_scopes_list
          | _ -> return valid_scopes_list
        
        in
        valid_scopes_list

    in

    let+ valid_scopes_list = find_highest_valid_scope_type_expr' tp in

    (* Logs.debug (fun m -> m "Rewriter.ProgUtils.find_highest_valid_scope_type_expr: valid_scopes_list = %a" (Print.pr_list_comma AstDef.QualIdent.pr) valid_scopes_list); *)

    Base.List.fold valid_scopes_list ~init:(Some AstDef.Predefs.prog_qual_ident) ~f:(fun qi scope ->
      let open Util.Option.Syntax in
      let rec compute_longer_qi q1 q2 = 
        match q1, q2 with
        | [], _ -> Some q2
        | _, [] -> Some q1
        | x :: xs, y :: ys -> 
          if not (Ident.equal x y) then
            None
          else
            let+ longer_qi = compute_longer_qi xs ys
            in
            x :: longer_qi
      
      in
      
      let* qi_unwrapped = qi in  
      let+ new_qi = compute_longer_qi (QualIdent.to_list qi_unwrapped) (QualIdent.to_list scope) in   
      
      (* Logs.debug (fun m -> m "Rewriter.ProgUtils.find_highest_valid_scope_type_expr: scope_found = %a" AstDef.QualIdent.pr (QualIdent.from_list new_qi)); *)

      QualIdent.from_list new_qi
    )


  

  (** Takes a type expression `tp` and introduces a module which implements Library.Type whose rep type T is `tp`. ~f here is expected to be Typing.process_symbol, but it's not hardcoded to prevent recursive dependencies  *)
  let intros_type_module ~(loc: location) ~(f: AstDef.Module.symbol -> AstDef.Module.symbol t) (tp: AstDef.type_expr) : qual_ident t =
    let mod_decl = begin
      let mod_name = 
        let mod_name_string = (AstDef.Type.to_string tp) ^ "$Type_Mod" in
        Ident.fresh loc (serialize mod_name_string)
      in

      {
        AstDef.Module.mod_decl_name = mod_name;
        mod_decl_formals = [];
        mod_decl_returns = Some Predefs.lib_type_mod_qual_ident;
        mod_decl_interfaces = Set.empty (module QualIdent);
        mod_decl_rep = Some Predefs.lib_type_rep_type_ident;
        mod_decl_is_ra = false;
        mod_decl_is_interface = false;
        mod_decl_loc = loc;
      }
    end in

    let (mod_def: AstDef.Module.module_instr list) = begin
      [
         SymbolDef (TypeDef {
          type_def_name = Predefs.lib_type_rep_type_ident;
          type_def_expr = Some tp;
          type_def_rep = true;
          type_def_loc = loc;
        });

      ]
    end in

    let symbol = AstDef.Module.ModDef { mod_decl; mod_def } in

    Logs.debug (fun m -> m "Rewriter.ProgUtils.intros_type_module: symbol = %a" AstDef.Symbol.pr symbol);

    (* let* topscope_name = find_highest_valid_scope_type_expr loc tp in

    let topscope_name = match topscope_name with
      | Some qi -> qi
      | None -> Error.type_error loc ("Could not find a valid scope to add type definition " ^ (AstDef.Type.to_string tp) ^ " to.") 
    
    in *)

    introduce_typecheck_symbol ~loc ~f symbol

  let rec does_symbol_implement_ra (symbol: AstDef.Module.symbol) : bool t =
    Logs.debug (fun m -> m "Rewriter.ProgUtils.does_symbol_implement_ra: symbol = %a" AstDef.Ident.pr (AstDef.Symbol.to_name symbol));
    let open Syntax in
    match symbol with
    | ModDef mod_def ->
      let mod_decl = mod_def.mod_decl in
      return mod_decl.mod_decl_is_ra
    | ModInst mod_inst ->
      
      let* does_type_implement_ra = 
        let* mod_inst_type_symbol = find_and_reify mod_inst.mod_inst_loc mod_inst.mod_inst_type in
        does_symbol_implement_ra mod_inst_type_symbol 
      in

      if does_type_implement_ra then
        return true
      else (
        match mod_inst.mod_inst_def with
        | None -> return false
        | Some (mod_inst_def_funct, mod_inst_def_args) ->
          
          let* mod_inst_def_funct_is_ra = 
            let* mod_inst_def_funct_symbol = find_and_reify mod_inst.mod_inst_loc mod_inst_def_funct in
            does_symbol_implement_ra mod_inst_def_funct_symbol in

          return mod_inst_def_funct_is_ra
      )
    | _ -> return false

  let rec does_type_implement_ra (tp: AstDef.type_expr) : bool t =
    let open Syntax in
    match tp with
    | App (Var qi, [], _) -> 
      let* symbol = find_and_reify (QualIdent.to_loc qi) (QualIdent.pop qi) in
      does_symbol_implement_ra symbol
    | _ -> return false

  let field_get_ra_qual_iden (field: AstDef.Module.field_def) = 
    let field_type = 
      match field.field_type with
      | App (Fld, [tp_expr], _) -> tp_expr
      | _ -> Error.error field.field_loc "Rewriter.ProgUtils.field_get_ra_module: Expected field definition"
    in

    match field_type with
    | App (Var qual_iden, [], _) -> QualIdent.pop qual_iden
    | _ -> Error.error field.field_loc "Rewriter.ProgUtils.field_get_ra_module: Expected field type to be a variable"

  let pred_get_ra_qual_iden (pred_qual_iden) =
    let open Syntax in
    let+ pred_fully_qual_iden = resolve (QualIdent.to_loc pred_qual_iden) pred_qual_iden in

    QualIdent.append (QualIdent.pop pred_fully_qual_iden) (pred_to_ra_mod_ident ~loc:(QualIdent.to_loc pred_qual_iden) (QualIdent.unqualify pred_fully_qual_iden))

  let au_get_ra_qual_iden (call_qual_iden) =
    let open Syntax in
    let+ call_fully_qual_iden = resolve (QualIdent.to_loc call_qual_iden) call_qual_iden in

    QualIdent.append (QualIdent.pop call_fully_qual_iden) (au_to_ra_mod_ident ~loc:(QualIdent.to_loc call_qual_iden) (QualIdent.unqualify call_fully_qual_iden))
    

  let get_ra_rep_type (ra_qual_iden: qual_ident) : type_expr =
    AstDef.Type.mk_var (QualIdent.to_loc ra_qual_iden) (QualIdent.append ra_qual_iden (Ident.make (QualIdent.to_loc ra_qual_iden) "T" 0))

  let get_ra_id (ra_qual_iden: qual_ident) : qual_ident =
    QualIdent.append ra_qual_iden (Ident.make (QualIdent.to_loc ra_qual_iden) "id" 0)

  let get_ra_valid_fn_qual_ident (ra_qual_iden: qual_ident) : qual_ident =
    QualIdent.append ra_qual_iden (Ident.make (QualIdent.to_loc ra_qual_iden) "valid" 0)

  let get_ra_comp_fn_qual_ident (ra_qual_iden: qual_ident) : qual_ident =
    QualIdent.append ra_qual_iden (Ident.make (QualIdent.to_loc ra_qual_iden) "comp" 0)

  let get_ra_frame_fn_qual_ident (ra_qual_iden: qual_ident) : qual_ident =
    QualIdent.append ra_qual_iden (Ident.make (QualIdent.to_loc ra_qual_iden) "frame" 0)

  let get_ra_fpu_allowed_qual_ident (ra_qual_iden: qual_ident) : qual_ident =
    QualIdent.append ra_qual_iden (Ident.make (QualIdent.to_loc ra_qual_iden) "fpuAllowed" 0)


  let field_utils_module_ident loc field_ident : ident =
    Ident.make loc (serialize ("FieldUtils$" ^ (Ident.to_string field_ident))) 0

  let pred_utils_module_ident loc pred_ident : ident =
    Ident.make loc (serialize ("PredUtils$" ^ (Ident.to_string pred_ident))) 0

  let au_utils_module_ident loc callable_ident : ident =
    Ident.make loc (serialize ("AUUtils$" ^ (Ident.to_string callable_ident))) 0



  let get_field_utils_module loc field_name : qual_ident t =
    let open Syntax in
    let+ field_fully_qual_name = resolve loc field_name in

    QualIdent.make field_fully_qual_name.qual_path (field_utils_module_ident loc field_fully_qual_name.qual_base)

  let get_pred_utils_module loc pred_name : qual_ident t =
    let open Syntax in
    let+ pred_fully_qual_name = resolve loc pred_name in

    QualIdent.make pred_fully_qual_name.qual_path (pred_utils_module_ident loc pred_fully_qual_name.qual_base)

  let get_au_utils_module loc call_name : qual_ident t =
    let open Syntax in
    let+ call_fully_qual_name = resolve loc call_name in

    QualIdent.make call_fully_qual_name.qual_path (au_utils_module_ident loc call_fully_qual_name.qual_base)



  let heap_utils_rep_type_ident loc = Ident.make loc "T" 0
  let get_field_utils_rep_type loc field_name : qual_ident t =
    let open Syntax in
    let+ field_utils_module = get_field_utils_module loc field_name in
    QualIdent.append field_utils_module (heap_utils_rep_type_ident loc)
  
  let get_pred_utils_rep_type loc pred_name : qual_ident t =
    let open Syntax in
    let+ pred_utils_module = get_pred_utils_module loc pred_name in
    QualIdent.append pred_utils_module (heap_utils_rep_type_ident loc)

  let get_au_utils_rep_type loc call_name : qual_ident t =
    let open Syntax in
    let+ call_utils_module = get_au_utils_module loc call_name in
    QualIdent.append call_utils_module (heap_utils_rep_type_ident loc)



  let heap_utils_comp_chunk_ident loc = Ident.make loc "heapChunkComp" 0
  let get_field_utils_comp loc field_name : qual_ident t =
    let open Syntax in
    let+ field_utils_module = get_field_utils_module loc field_name in
    QualIdent.append field_utils_module (heap_utils_comp_chunk_ident loc)

  let get_pred_utils_comp loc pred_name : qual_ident t =
    let open Syntax in
    let+ pred_utils_module = get_pred_utils_module loc pred_name in
    QualIdent.append pred_utils_module (heap_utils_comp_chunk_ident loc)

  let get_au_utils_comp loc call_name : qual_ident t =
    let open Syntax in
    let+ call_utils_module = get_au_utils_module loc call_name in
    QualIdent.append call_utils_module (heap_utils_comp_chunk_ident loc)



  let heap_utils_frame_chunk_ident loc = Ident.make loc "heapChunkFrame" 0
  let get_field_utils_frame loc field_name : qual_ident t =
    let open Syntax in
    let+ field_utils_module = get_field_utils_module loc field_name in
    QualIdent.append field_utils_module (heap_utils_frame_chunk_ident loc)

  let get_pred_utils_frame loc pred_name : qual_ident t =
    let open Syntax in
    let+ pred_utils_module = get_pred_utils_module loc pred_name in
    QualIdent.append pred_utils_module (heap_utils_frame_chunk_ident loc)

  let get_au_utils_frame loc call_name : qual_ident t =
    let open Syntax in
    let+ call_utils_module = get_au_utils_module loc call_name in
    QualIdent.append call_utils_module (heap_utils_frame_chunk_ident loc)



  let heap_utils_valid_ident loc = Ident.make loc "valid" 0
  let get_field_utils_valid loc field_name : qual_ident t =
    let open Syntax in
    let+ field_utils_module = get_field_utils_module loc field_name in
    QualIdent.append field_utils_module (heap_utils_valid_ident loc)

  let get_pred_utils_valid loc pred_name : qual_ident t =
    let open Syntax in
    let+ pred_utils_module = get_pred_utils_module loc pred_name in
    QualIdent.append pred_utils_module (heap_utils_valid_ident loc)

  let get_au_utils_valid loc call_name : qual_ident t =
    let open Syntax in
    let+ call_utils_module = get_au_utils_module loc call_name in
    QualIdent.append call_utils_module (heap_utils_valid_ident loc)

  let heap_utils_heapchunk_compare_ident loc = Ident.make loc "heapChunkCompare" 0
  let get_field_utils_heapchunk_compare loc field_name : qual_ident t =
    let open Syntax in
    let+ field_utils_module = get_field_utils_module loc field_name in
    QualIdent.append field_utils_module (heap_utils_heapchunk_compare_ident loc)

  let get_pred_utils_heapchunk_compare loc pred_name : qual_ident t =
    let open Syntax in
    let+ pred_utils_module = get_pred_utils_module loc pred_name in
    QualIdent.append pred_utils_module (heap_utils_heapchunk_compare_ident loc)

  let get_au_utils_heapchunk_compare loc call_name : qual_ident t =
    let open Syntax in
    let+ call_utils_module = get_au_utils_module loc call_name in
    QualIdent.append call_utils_module (heap_utils_heapchunk_compare_ident loc)



  let heap_utils_id_ident loc = Ident.make loc "id" 0
  let get_field_utils_id loc field_name : expr t =
    let open Syntax in
    let* field_utils_module = get_field_utils_module loc field_name in

    let* field = find_and_reify loc field_name in
    let field_type = 
      match field with
      | AstDef.Module.FieldDef { field_type; _ } -> field_type
      | _ -> Error.error loc "Rewriter.ProgUtils.get_field_utils_id: Expected field definition"
    in

    let field_elem_type = match field_type with
      | App (Fld, [tp], _) -> tp
      | _ -> Error.error loc "Rewriter.ProgUtils.get_field_utils_id: Expected field type"
    in

    let id_qual_ident = QualIdent.append field_utils_module (heap_utils_id_ident loc)

    in

    return @@ AstDef.Expr.mk_var ~loc id_qual_ident ~typ:field_elem_type

  let get_pred_utils_id loc pred_name : expr t =
    let open Syntax in
    let* pred_utils_module = get_pred_utils_module loc pred_name in

    let* pred = find_and_reify loc pred_name in

    let* pred_elem_type_name = get_pred_utils_rep_type loc pred_name in
    
    let pred_elem_type = AstDef.Type.mk_var loc pred_elem_type_name in

    let id_qual_ident = QualIdent.append pred_utils_module (heap_utils_id_ident loc)

    in

    return @@ AstDef.Expr.mk_var ~loc id_qual_ident ~typ:pred_elem_type

  let get_au_utils_id loc call_name : expr t =
    let open Syntax in
    let* call_utils_module = get_au_utils_module loc call_name in

    let* call = find_and_reify loc call_name in

    let* call_elem_type_name = get_au_utils_rep_type loc call_name in
    
    let call_elem_type = AstDef.Type.mk_var loc call_elem_type_name in

    let id_qual_ident = QualIdent.append call_utils_module (heap_utils_id_ident loc)

    in

    return @@ AstDef.Expr.mk_var ~loc id_qual_ident ~typ:call_elem_type

  let pred_ra_constr_qual_ident loc pred_name =
    let open Syntax in
    let* pred_ra_qual_iden = pred_get_ra_qual_iden pred_name in

    let+ pred = find_and_reify loc pred_name in
    match pred with
    | AstDef.Module.CallDef c ->
      (match c.call_decl.call_decl_kind with
      | Pred ->
        QualIdent.append pred_ra_qual_iden AstDef.Predefs.lib_countAgreeRA_constr_ident

      | Invariant ->
        QualIdent.append pred_ra_qual_iden AstDef.Predefs.lib_agree_constr_ident

      | _ -> Error.error loc "Rewriter.ProgUtils.pred_ra_constr_qual_ident: Expected pred definition" 
      )

    | _ -> Error.error loc "Rewriter.ProgUtils.pred_ra_constr_qual_ident: Expected pred definition"

  let au_ra_uncommitted_constr_qual_ident loc call_name = 
    let open Syntax in
    let+ call_ra_qual_iden = au_get_ra_qual_iden call_name in

    QualIdent.append call_ra_qual_iden AstDef.Predefs.lib_atomic_token_uncommitted_constr_ident

  let au_ra_committed_constr_qual_ident loc call_name = 
    let open Syntax in
    let+ call_ra_qual_iden = au_get_ra_qual_iden call_name in

    QualIdent.append call_ra_qual_iden AstDef.Predefs.lib_atomic_token_committed_constr_ident
    

  let pred_ra_count_destr_qual_ident loc pred_name =
    let open Syntax in
    let+ pred_ra_qual_iden = pred_get_ra_qual_iden pred_name in
    QualIdent.append pred_ra_qual_iden AstDef.Predefs.lib_countAgreeRA_destr1_ident

  let pred_ra_val_destr_qual_ident loc pred_name =
    let open Syntax in
    let* pred_ra_qual_iden = pred_get_ra_qual_iden pred_name in

    let+ pred = find_and_reify loc pred_name in
    match pred with
    | AstDef.Module.CallDef c ->
      (match c.call_decl.call_decl_kind with
      | Pred ->
        QualIdent.append pred_ra_qual_iden AstDef.Predefs.lib_countAgreeRA_destr2_ident

      | Invariant ->
        QualIdent.append pred_ra_qual_iden AstDef.Predefs.lib_agree_destr1_ident

      | _ -> Error.error loc "Rewriter.ProgUtils.pred_ra_constr_qual_ident: Expected pred definition" 
      )

    | _ -> Error.error loc "Rewriter.ProgUtils.pred_ra_constr_qual_ident: Expected pred definition"

  let pred_in_types pred_name =
    let open Syntax in
    let+ pred = find_and_reify (AstDef.QualIdent.to_loc pred_name) pred_name in

    match pred with
    | AstDef.Module.CallDef c when Poly.(c.call_decl.call_decl_kind = Pred || c.call_decl.call_decl_kind = Invariant)  ->
      Base.List.map c.call_decl.call_decl_formals ~f:(fun var_decl -> var_decl.var_type)

    | _ -> Error.error (AstDef.QualIdent.to_loc pred_name) "Rewriter.ProgUtils.pred_in_types: Expected pred definition"

  let pred_out_types pred_name =
    let open Syntax in
    let+ pred = find_and_reify (AstDef.QualIdent.to_loc pred_name) pred_name in

    match pred with
    | AstDef.Module.CallDef c when Poly.(c.call_decl.call_decl_kind = Pred || c.call_decl.call_decl_kind = Invariant)  ->
      Base.List.map c.call_decl.call_decl_returns ~f:(fun var_decl -> var_decl.var_type)

    | _ -> Error.error (AstDef.QualIdent.to_loc pred_name) "Rewriter.ProgUtils.pred_in_types: Expected pred definition"

  let pred_heap_type pred_name =
    let open Syntax in
    let* pred_in_types = pred_in_types pred_name in

    let+ pred_rep_type = get_pred_utils_rep_type (QualIdent.to_loc pred_name) pred_name in
    
    AstDef.Type.mk_map (QualIdent.to_loc pred_name) (AstDef.Type.mk_prod (QualIdent.to_loc pred_name) pred_in_types) (AstDef.Type.mk_var (QualIdent.to_loc pred_name) pred_rep_type)

  let rec is_expr_pure (expr: expr)  : (bool, 'a) t_ext =
    let open Syntax in
    match expr with
    
    | App (constr, expr_list, _) ->
      let* b1 = 
      (match constr with
      | Own -> return false
      | Var qual_ident ->
        if AstDef.QualIdent.is_local qual_ident then
          return true
        else
        let* _, symbol, _ = find (AstDef.Expr.to_loc expr) qual_ident in
        (match symbol with
        | CallDef c -> (match c.call_decl.call_decl_kind with 
          | Func -> return true 
          | _ -> return false)
        | FieldDef _ -> return false
        | VarDef _  | ConstrDef _ | DestrDef _  -> return true
        | _ -> Error.error (AstDef.Expr.to_loc expr) "Rewriter.ProgUtils.is_expr_pure: Expected a function or a variable"
        )
      | _ -> return true
      ) in
  
      let* expr_list_pure = (List.map expr_list ~f:is_expr_pure) in
      let b2 = Base.List.fold_left ~init:true expr_list_pure ~f:(&&) in
  
      return (b1 && b2)

    | Binder (_binder, _var_decls, _trgs, expr, _) ->
      is_expr_pure expr


  let get_data_destrs_from_constr (qual_ident: qual_ident) : (qual_ident list) t =
    let open Syntax in
    let* symbol = find_and_reify (AstDef.QualIdent.to_loc qual_ident) qual_ident in
    match symbol with
    | AstDef.Module.ConstrDef constr_def ->

      let tp_name = match constr_def.constr_return_type with
        | App (Var qi, _, _) -> qi
        | _ -> Error.error (AstDef.QualIdent.to_loc qual_ident) "Rewriter.ProgUtils.get_data_destrs_from_constr: Expected a variable"
      in

      let* symbol = find_and_reify (AstDef.QualIdent.to_loc tp_name) tp_name in
      (match symbol with
      | AstDef.Module.TypeDef { type_def_expr = Some tp_expr; _ } ->
        (match tp_expr with
        | App (Data (_, variant_decls), [], _) ->
          let variant_decl = Base.List.find variant_decls ~f:(fun variant_decl -> Ident.equal variant_decl.variant_name qual_ident.qual_base) in

          (match variant_decl with
          | None -> Error.error (AstDef.QualIdent.to_loc qual_ident) "Rewriter.ProgUtils.get_data_destrs_from_constr: Expected a variant declaration"
          | Some variant_decl ->
            return (Base.List.map variant_decl.variant_args ~f:(fun var_decl -> QualIdent.append (QualIdent.pop qual_ident) var_decl.var_name)))

        | _ ->
          Error.error (AstDef.QualIdent.to_loc qual_ident) "Rewriter.ProgUtils.get_data_destrs_from_constr: Expected a data type"

        )
      
      | _ -> Error.error (AstDef.QualIdent.to_loc qual_ident) "Rewriter.ProgUtils.get_data_destrs_from_constr: Expected a type definition"
      )

    | _ -> Error.error (AstDef.QualIdent.to_loc qual_ident) "Rewriter.ProgUtils.get_data_destrs_from_constr: Expected a constructor definition"


  let rec expr_preds_mentioned (expr: AstDef.Expr.t) : ((QualIdent.t list), 'a) t_ext =
  let open Syntax in 
  match expr with
  | App (Var qual_ident, _, _) ->
    let+ _, (_, symbol, _) = resolve_and_find (AstDef.Expr.to_loc expr) qual_ident in

    (match symbol with
    | CallDef c -> 
      (match c.call_decl.call_decl_kind with
      | Pred | Invariant -> [qual_ident]
      | _ -> []
      )
    | _ -> []
    )
  | App (_, expr_list, _) ->
    List.fold_right expr_list ~init:([]) ~f:(fun expr acc ->
      let+ expr_predicates = expr_preds_mentioned expr in
      (acc @ expr_predicates)
    )

  | Binder (_, _, _, expr, _) ->
    expr_preds_mentioned expr
  
  let stmt_preds_mentioned (s: AstDef.Stmt.t) : ((QualIdent.t list), 'a) t_ext = 
    let open Syntax in
    let rec stmt_preds_mentioned (s: AstDef.Stmt.t) : (QualIdent.t list) t =
      match s.stmt_desc with
      | Block b -> 
        let* block_preds = List.map b.block_body ~f:stmt_preds_mentioned in
  
        return (Base.List.concat block_preds)
      
      | Loop l ->
        let* prebody_preds = stmt_preds_mentioned l.loop_prebody in
        (* let* test_preds = expr_preds_mentioned l.loop_test in *)
        let* postbody_preds = stmt_preds_mentioned l.loop_postbody in
  
        (* return (prebody_preds @ test_preds @ postbody_preds) *)
        return (prebody_preds @ postbody_preds)
  
      | Cond c ->
        (* let* test_preds = expr_preds_mentioned c.cond_test in *)
        let* then_preds = stmt_preds_mentioned c.cond_then in
        let* else_preds = stmt_preds_mentioned c.cond_else in
  
        (* return (test_preds @ then_preds @ else_preds) *)
        return (then_preds @ else_preds)
  
      | Basic s ->
        begin match s with
        | Spec (_, sp) -> 
          expr_preds_mentioned sp.spec_form
        
        | Use u ->
          return [u.use_name]
        
        | _ -> return []
        end
  
      in
  
    let* preds_list = stmt_preds_mentioned s in
    let preds_list = Base.List.dedup_and_sort preds_list ~compare:QualIdent.compare in
  
    return preds_list
    
end
