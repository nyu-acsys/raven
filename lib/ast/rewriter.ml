open Base
open AstDef
open Util

type state = {
  state_table: SymbolTbl.t;
  state_update_table: bool;
  state_new_symbols: Module.symbol list list;
}
  
type 'a t = state -> (state * 'a)

let return a = fun s -> (s, a)
                           
module Syntax = struct
  (* For ppx_let *)
  module Let_syntax = struct
    let bind m ~f = fun sin ->
      let sout, res = m sin in
      f res sout

    let return = return

    let map m ~f = fun sin ->
      let sout, res = m sin in
      (sout, f res)
      
    let both m1 m2 = fun sin ->
      let s1, res1 = m1 sin in
      let s2, res2 = m2 s1 in
      (s2, (res1, res2))
  end
    
  open Let_syntax
  
  let (let+) m f = map m ~f
  let (and+) = both
  let (let* ) m f = bind m ~f
  let (and* ) = both
  
end

      
let eval ?(update=true) m tbl =
  let sin =
    { state_table = tbl;
      state_update_table = update;
      state_new_symbols = [];
    }
  in
  let sout, res = m sin in
  sout.state_table, res
    
let init s _ = s, ()
                             
let get_table s = s, s.state_table

let update_table f s =
  { s with state_table = f s.state_table },
  ()

let exit_module mdef s =
  let tbl = s.state_table in
  let new_symbols, mdef = 
    match s.state_new_symbols with
    | symbols :: new_symbols ->
      let open Module in
      let new_instr = List.rev_map ~f:(fun def -> SymbolDef def) symbols in
      new_symbols,      
      { mdef with mod_def = new_instr @ mdef.mod_def }
    | new_symbols -> new_symbols, mdef
  in
  { s with
    state_table = SymbolTbl.exit tbl;
    state_new_symbols = new_symbols
  },
  mdef


let exit_callable call_def s =
  let tbl = s.state_table in
  let new_symbols, call_def =
    match s.state_new_symbols with
    | new_callable_symbols :: new_mod_symbols :: new_symbols ->
      let open Callable in
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
      (new_mod_symbols1 @ new_mod_symbols) :: new_symbols,
      { call_def with call_decl }
    | new_symbols -> new_symbols, call_def
  in
  { s with
    state_table = SymbolTbl.exit tbl;
    state_new_symbols = new_symbols
  },
  call_def

let enter symbol s =
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

let enter_callable callable = enter (CallDef callable)

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


let add_locals var_decls s =
  if s.state_update_table
  then update_table (SymbolTbl.add_local_vars var_decls) s
  else s, ()

let add_call_decl_locals (call_decl : Callable.call_decl) =
  let open Syntax in
  let+ _ =  add_locals call_decl.call_decl_formals
  and+ _ = add_locals call_decl.call_decl_returns
  and+ _ = add_locals call_decl.call_decl_locals in
  ()

let set_symbol symbol s =
  if s.state_update_table
  then { s with state_table = SymbolTbl.set_symbol symbol s.state_table }, ()
  else s, ()

let import import_instr s =
  { s with state_table = SymbolTbl.import import_instr s.state_table },
  ()

module List = struct

  let map (xs : 'a list) ~(f : 'a -> 'b t) : 'b list t = fun s ->
    List.fold_map xs ~init:s ~f:(fun s x -> f x s)

  let map2 (xs : 'a list) (ys : 'b list) ~f = fun s ->
    match List.zip xs ys with
    | Ok xs_ys ->
      let s, res = List.fold_map xs_ys ~init:s ~f:(fun s (x, y) -> f x y s) in
      s, Base.List.Or_unequal_lengths.Ok res
    | Unequal_lengths -> s, Unequal_lengths

  let fold_right (xs : 'a list) ~(init : 'b) ~f : 'b t = fun s -> 
    List.fold_right xs ~f:(fun x (s, acc) -> f x acc s) ~init:(s, init) 
        
  let fold_map xs ~init ~f = fun s ->
    let (s, acc), ys = List.fold_map xs ~init:(s, init)
        ~f:(fun (s, acc) x ->
            let s, (acc, y) = f acc x s in
            (s, acc), y)
    in
    s, (acc, ys)
  
  let iter xs ~f = fun s ->
    List.fold_left xs ~init:s ~f:(fun s x -> let res, () = f x s in res), ()
end

module Option = struct

  let map (x: 'a option) ~(f: 'a -> 'b t): 'b option t = 
    let open Syntax in
    match x with
    | None -> return None
    | Some v ->
      let+ res = f v in
      Some res
end

module Type = struct
  let descend ~f (tp_expr: Type.t) : Type.t t =
    let open Syntax in
    match tp_expr with
    | App (constr, tp_list, tp_attr) ->
      let+ tp_list = List.map tp_list ~f in
      Type.App (constr, tp_list, tp_attr)

  let rec rewrite_qual_idents ~f (tp_expr: Type.t) : Type.t t =
    match tp_expr with
    | App (Var id, [], tp_attr) ->
      return (Type.App (Var (f id), [], tp_attr))
    | _ -> descend ~f:(rewrite_qual_idents ~f) tp_expr
  
end

module VarDecl = struct

  let rewrite_types ~f var_decl : var_decl t =
    let open Syntax in
    let+ var_type = f var_decl.AstDef.Type.var_type in
    { var_decl with var_type = var_type }  
end

module Expr = struct
  let descend ~f (expr: Expr.t) : Expr.t t =
    let open Syntax in
    match expr with
    | App (constr, expr_list, expr_attr) ->
      let+ expr_list = List.map expr_list ~f in
      Expr.App (constr, expr_list, expr_attr)

    | Binder (b, v_l, inner_expr, expr_attr) ->
      let+ _ = add_locals v_l
      and+ inner_expr = f inner_expr in    
      Expr.Binder (b, v_l, inner_expr, expr_attr)

  let rec rewrite_types ~(f: AstDef.Type.t -> AstDef.Type.t t) (expr: Expr.t) : Expr.t t =
    let open Syntax in
    match expr with
    | App (constr, expr_list, expr_attr) ->
      let+ expr_list = List.map expr_list ~f:(rewrite_types ~f)
      and+ expr_type = f expr_attr.expr_type in
      let expr_attr = { expr_attr with expr_type = expr_type } in
      Expr.App (constr, expr_list, expr_attr)

    | Binder (b, var_decls, inner_expr, expr_attr) ->
      let* var_decls = List.map var_decls ~f:(VarDecl.rewrite_types ~f) in
      let+ _ = add_locals var_decls
      and+ inner_expr = rewrite_types ~f inner_expr in
      Expr.Binder (b, var_decls, inner_expr, expr_attr)
    
  let rec rewrite_qual_idents ~f (expr: Expr.t) : Expr.t t =
    let open Syntax in
    match expr with
    | App (constr, expr_list, expr_attr) ->
      let+ expr_list = List.map expr_list ~f:(rewrite_qual_idents ~f)
      and+ expr_type = Type.rewrite_qual_idents ~f expr_attr.expr_type in
      let expr_attr = { expr_attr with expr_type = expr_type } in
      let constr = match constr with
        | Var qual_ident -> Expr.Var (f qual_ident)
        | Call (qual_ident, loc) -> Expr.Call (f qual_ident, loc)
        | DataConstr (qual_ident, loc) -> Expr.DataConstr (f qual_ident, loc)
        | DataDestr (qual_ident, loc) -> Expr.DataDestr (f qual_ident, loc)
        | _ -> constr
      in
      Expr.App (constr, expr_list, expr_attr)

    | Binder (b, var_decls, inner_expr, expr_attr) ->
      let* var_decls = List.map var_decls ~f:(VarDecl.rewrite_types ~f:(Type.rewrite_qual_idents ~f)) in
      let+ _ = add_locals var_decls
      and+ inner_expr = rewrite_qual_idents ~f inner_expr in
      Expr.Binder (b, var_decls, inner_expr, expr_attr)
    
end

module Stmt = struct
  let descend ~(f: Stmt.t -> Stmt.t t) (stmt: Stmt.t) : Stmt.t t =
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
  
  let rewrite_expressions_top ~f ~c (stmt: Stmt.t) : Stmt.t t =
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
      let+ new_expr = f assign.assign_rhs in
      { stmt with stmt_desc = Basic (Assign { assign with assign_rhs = new_expr; }); }

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
      let+ fpu_val = f fpu_desc.fpu_val in
      { stmt with stmt_desc = Basic (Fpu { fpu_desc with fpu_val }) }


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

  let rec rewrite_expressions ~f stmt : Stmt.t t =
    rewrite_expressions_top ~f ~c:(rewrite_expressions ~f) stmt
  
  let rec rewrite_types ~f stmt : Stmt.t t =
    let open Syntax in
    match stmt.Stmt.stmt_desc with
    | Stmt.Basic (VarDef var_def) ->
      let* var_decl = VarDecl.rewrite_types ~f var_def.var_decl
      and* new_init = Option.map var_def.var_init ~f:(Expr.rewrite_types ~f) in
      let+ _ = add_locals [var_decl] in
      { stmt with stmt_desc = Basic (VarDef { var_decl = var_decl; var_init = new_init; }); }
    | _ -> rewrite_expressions_top ~f:(Expr.rewrite_types ~f) ~c:(rewrite_types ~f) stmt

  let rec rewrite_qual_idents ~f stmt : Stmt.t t =
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
        and+ fpu_val = Expr.rewrite_qual_idents ~f fpu_desc.fpu_val in
        { stmt with stmt_desc = Basic (Fpu { fpu_ref; fpu_field; fpu_val }) }

      (* TODO: add remaining *)
      | _ -> rewrite_expressions_top ~f:(Expr.rewrite_qual_idents ~f) ~c:(rewrite_qual_idents ~f) stmt
      end

    | _ -> rewrite_expressions_top ~f:(Expr.rewrite_qual_idents ~f) ~c:(rewrite_qual_idents ~f) stmt
end

module Callable = struct

  let rewrite_expressions_top ~(fe:expr -> expr t) ~fs callable : Callable.t t =
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
      let+ proc_body = Option.map proc_body ~f:fs in
      Callable.{ call_decl; call_def = Callable.ProcDef { proc_body } }   

  let rewrite_scoped ~f callable =
    let open Syntax in
    let* _ = enter_callable callable in
    let* callable = f callable in
    exit_callable callable    
  
  let rewrite_expressions ~f callable =
    rewrite_scoped ~f:(rewrite_expressions_top ~fe:f ~fs:(Stmt.rewrite_expressions ~f)) callable
  
  let rewrite_types_top ~(ft:type_expr -> type_expr t) ~fe ~fs callable : Callable.t t =
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

    

  let rewrite_qual_idents ~f callable =
    rewrite_scoped
      ~f:(rewrite_types_top
            ~ft:(Type.rewrite_qual_idents ~f)
            ~fe:(Expr.rewrite_qual_idents ~f)
            ~fs:(Stmt.rewrite_qual_idents ~f))
      callable
  
end

module Module = struct

  let rec rewrite_symbols ~f (mdef: Module.t) : Module.t t =
    let open Module in
    let open Syntax in
    let* _ = enter_module mdef
    and* symbols = List.map mdef.mod_def ~f:(function
        | SymbolDef (ModDef sub_mdef) ->
          let+ sub_mdef = rewrite_symbols ~f sub_mdef 
          and+ _ = set_symbol (ModDef sub_mdef) in
          SymbolDef (ModDef sub_mdef)
        | SymbolDef symbol ->
            let+ symbol = f symbol
            and+ _ = set_symbol symbol in
            SymbolDef symbol
        | import -> return import 
      )
    in
    let mdef = { mdef with mod_def = symbols } in
    exit_module mdef
    
  let rewrite_expressions ~f mdef : Module.t t =
    let open Syntax in
    let open Module in
    let rewrite_symbol = function
      | VarDef var_def ->
        let+ new_var_init = Option.map var_def.var_init ~f in
        VarDef { var_def with var_init = new_var_init }
      | CallDef call_def ->
        let+ new_call_def = Callable.rewrite_expressions ~f call_def in
        CallDef new_call_def
      | mem_def -> return mem_def
    in
    rewrite_symbols ~f:rewrite_symbol mdef

  let rewrite_types ~f mdef : Module.t t =
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
        let+ new_call_def = Callable.rewrite_types ~f call_def in
        CallDef new_call_def
      | mem_def -> return mem_def
    in
    rewrite_symbols ~f:rewrite_symbol mdef

  let rec rewrite_qual_idents_in_symbol ~(f: QualIdent.t -> QualIdent.t) : Module.symbol -> Module.symbol t =
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
        let+ new_call_def = Callable.rewrite_qual_idents ~f call_def in
        CallDef new_call_def
      | ModDef mod_def ->
        let+ new_mod_def = rewrite_qual_idents ~f mod_def in
        ModDef new_mod_def

  and rewrite_qual_idents ~f mdef : Module.t t =
    (* TODO: rewrite imports *)
    rewrite_symbols ~f:(rewrite_qual_idents_in_symbol ~f) mdef  
end

module Symbol = struct
  let reify (name, symbol, subst) =
    let open Syntax in
    let+ tbl = get_table in
    let tbl_scope = SymbolTbl.goto (AstDef.Symbol.to_loc symbol) name tbl in
    let _, symbol1 = eval (Module.rewrite_qual_idents_in_symbol ~f:(QualIdent.requalify subst) symbol) tbl_scope in
    symbol1

  let reify_type_def loc (_name, symbol, subst) : AstDef.Type.t Base.Option.t t =
    let open Syntax in
    match symbol with
    | AstDef.Module.TypeDef { type_def_expr = None; _ } ->
      return None
    | TypeDef { type_def_expr = Some tp_expr; _ } -> 
      let+ tp_expr = Type.rewrite_qual_idents ~f:(QualIdent.requalify subst) tp_expr in
      Some tp_expr
    | _ -> Error.error loc "Expected type identifier"

  let reify_type loc (_name, symbol, subst) : AstDef.Type.t t =
    let tp_expr =
      match symbol with
      | AstDef.Module.VarDef { var_decl; _ } -> var_decl.var_type
      | FieldDef field_def -> field_def.field_type
      | _ -> Error.error loc "Expected expression identifier"
    in
    Type.rewrite_qual_idents ~f:(QualIdent.requalify subst) tp_expr
      
  let reify_field_type loc (_name, symbol, subst) : AstDef.Type.t t =
    let tp_expr =
      match symbol with
      | AstDef.Module.FieldDef { field_type = App(Fld, [tp], _); _ } -> tp
      | _ -> Error.error loc "Expected field identifier"
    in
    Type.rewrite_qual_idents ~f:(QualIdent.requalify subst) tp_expr

  
  let orig_symbol (_name, symbol, _subst) = symbol

  let extract (symbol, subst) ~f =
    f (QualIdent.requalify subst) symbol

  let add_subst s (name, symbol, subst) = (name, symbol, s :: subst)
  
  type t = QualIdent.t * AstDef.Module.symbol * QualIdent.subst
                                 
end

let resolve_and_find loc name : (QualIdent.t * Symbol.t) t =
  let open Syntax in
  let+ tbl = get_table in
  let alias_qual_ident, qual_ident, symbol, subst = SymbolTbl.resolve_and_find_exn loc name tbl in
  qual_ident, (alias_qual_ident, symbol, subst)

let resolve loc name : QualIdent.t t =
  let open Syntax in
  let+ qual_ident, _ = resolve_and_find loc name in
  qual_ident


let find loc name : Symbol.t t =
  let open Syntax in
  let+ _, symbol = resolve_and_find loc name in
  symbol
