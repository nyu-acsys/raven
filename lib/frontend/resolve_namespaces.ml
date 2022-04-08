(** Resolve identifiers to make everything unique*)
open Base
open Ast
(* open Util *)

module SymbolTbl = struct
(*   module IdentMap = Map.M(Ident)
  type 'a ident_map = 'a IdentMap.t *)

  type qual_qual_ident_map = qual_ident qual_ident_map

  (* type t = (ident ident_map) list *)

  type t = (ident option * qual_qual_ident_map) list


  let label_to_string label = match label with
  | None -> "__"
  | Some iden -> Ident.to_string iden

  let rec map_to_string t = match t with
  | [] -> " "
  | (k,v) :: ms -> (QualIdent.to_string k ^ " -> " ^ QualIdent.to_string v ^ "\n") ^ (map_to_string ms)

  let rec to_string tbl = match tbl with
    | [] -> "end\n\n"
    | t :: ts -> label_to_string (fst t) ^ " :: [ " ^ map_to_string (Map.to_alist (snd t)) ^ " ]\n" ^ (to_string ts)

  let push ?(name = None) tbl : t = (name, Map.empty (module QualIdent)) :: tbl

  let push_name name tbl = push ~name:(Some name) tbl

  let pop tbl = match tbl with
  | [] -> raise(Failure "Empty symbol table")
  | _ :: ts -> ts


  let rec fully_qualified (id: qual_ident) tbl = match tbl with
    | [] -> id
    | (label, _) :: ts -> match label with
        | None -> id
        | Some iden -> fully_qualified (QualIdent.left_append iden id) ts


  let rec add_helper tbl name fq_id =
    match tbl with
    | [] -> []
    | t :: ts -> let (label, map) = t in
          let t' = 
            try
              (label, (Map.add_exn (map) ~key:name ~data:fq_id)) 
            with _ -> raise(Failure ("duplicate exists: " ^ QualIdent.to_string name ^ " to " ^ QualIdent.to_string fq_id))
          in
          let ts' = match label with
              | None -> ts
              | Some iden -> add_helper ts (QualIdent.left_append iden name) fq_id

          in
          t' :: ts'

  let add tbl name id = 
    print_debug ("ADDING " ^ QualIdent.to_string name ^ " -> " ^ QualIdent.to_string id ^ "\n" ^ to_string tbl);
    let fully_qual_id = fully_qualified id tbl in
  match tbl with
    | [] -> raise(Failure "Empty symbol table")
    | tbl -> add_helper tbl name fully_qual_id

 (*  let remove tbl name = print_debug ("Removing " ^ QualIdent.to_string name ^ "\n" ^ to_string tbl);
  match tbl with
    | [] -> raise(Failure "Empty symbol table")
    | t :: ts -> let (label, map) = t in
        (label, (Map.remove map name)) :: ts
        *)                                     
(*   let declared_in_current tbl name =
    Map.mem (fst (List.hd tbl)) name 
 *)

  let find_local tbl name =
    match tbl with
    | [] -> None
    | (_, map) :: _ -> Map.find name map

  let rec find tbl name = match tbl with
    | [] -> None
    | (_, map) :: ts -> match (Map.find map name) with
        | None -> find ts name
        | Some id -> Some id
end

let option_disambiguate fn arg tbl = match arg with
  | None -> None, tbl
  | Some s -> let s', tbl = fn s tbl in
      (Some s'), tbl

let rec list_disambiguate fn arg tbl = match arg with
  | [] -> [], tbl
  | l :: ls -> let l', tbl = fn l tbl in
      let ls', tbl = list_disambiguate fn ls tbl 
        in ((l' :: ls'), tbl)

module IdentDisambiguate = struct
  let old_ident_disambiguate iden (tbl: SymbolTbl.t) = print_debug ("Old_Ident: " ^ Ident.to_string iden ^ "\n");
    match (SymbolTbl.find tbl (QualIdent.from_ident iden)) with
    | None -> raise(Failure ("Variable Not Ref: " ^ Ident.to_string iden))
    | Some id -> id.qual_base, tbl
  
  let new_ident_disambiguate iden (tbl: SymbolTbl.t) = print_debug ("New_Ident: " ^ Ident.to_string iden ^ "\n");
    let iden' = Ident.fresh iden.ident_name in
    let tbl = SymbolTbl.add tbl (QualIdent.from_ident iden) (QualIdent.from_ident iden') in
    iden', tbl

end

let old_ident_disambiguate = IdentDisambiguate.old_ident_disambiguate
let new_ident_disambiguate = IdentDisambiguate.new_ident_disambiguate

let ident_map_new_disambiguate val_fun id_map tbl = 
  let fn (id, value) tbl =
    let id', tbl = new_ident_disambiguate id tbl in
    let value', tbl = val_fun value tbl in
    (id', value'), tbl

  in
  let rec fn_iter l tbl = match l with
    | [] -> [], tbl
    | (id, value) :: ls -> 
        let (id', value'), tbl = fn (id, value) tbl in
        let ls', tbl = fn_iter ls tbl in
          ((id', value') :: ls'), tbl

  in let l', tbl = fn_iter (Map.to_alist id_map) tbl
in (Map.of_alist_exn (module Ident) l'), tbl

let ident_map_old_disambiguate val_fun id_map tbl = 
  let fn (id, value) tbl =
    let value', tbl = val_fun value tbl in
    let id', tbl = old_ident_disambiguate id tbl in
    (id', value'), tbl

  in
  let rec fn_iter l tbl = match l with
    | [] -> [], tbl
    | (id, value) :: ls -> 
        let (id', value'), tbl = fn (id, value) tbl in
        let ls', tbl = fn_iter ls tbl in
          ((id', value') :: ls'), tbl

  in let l', tbl = fn_iter (Map.to_alist id_map) tbl
in (Map.of_alist_exn (module Ident) l'), tbl

module QualIdentDisambiguate = struct
  let rec qual_ident_disambiguate (qual_iden : qual_ident) tbl =
    print_debug ("Old_QualIdent: " ^ QualIdent.to_string qual_iden ^ "\n");
    match (SymbolTbl.find tbl qual_iden) with
    | None -> raise(Failure ("Variable Not Ref: " ^ QualIdent.to_string qual_iden))
    | Some id -> id, tbl
end

let qual_ident_disambiguate = QualIdentDisambiguate.qual_ident_disambiguate

module TypeDisambiguate = struct
  let rec type_attr_disambiguate tp_attr tbl = tp_attr, tbl

  and var_decl_disambiguate (var_decl : Type.var_decl) tbl =
    let var_name', tbl = new_ident_disambiguate var_decl.var_name tbl in
    let var_loc' = var_decl.var_loc in
    let var_type', tbl = type_disambiguate var_decl.var_type tbl in
    let var_const' = var_decl.var_const in
    let var_ghost' = var_decl.var_ghost in
    let var_implicit' = var_decl.var_implicit in

    let (var_decl' : Type.var_decl) = 
    { var_name = var_name';
      var_loc = var_loc';
      var_type = var_type';
      var_const = var_const';
      var_ghost = var_ghost';
      var_implicit = var_implicit';
    } 

  in var_decl', tbl

  and struct_var_decl_disambiguate (var_decl : Type.var_decl) tbl =
  let var_name', tbl = var_decl.var_name, tbl in
  let var_loc' = var_decl.var_loc in
  let var_type', tbl = type_disambiguate var_decl.var_type tbl in
  let var_const' = var_decl.var_const in
  let var_ghost' = var_decl.var_ghost in
  let var_implicit' = var_decl.var_implicit in

  let (var_decl' : Type.var_decl) = 
  { var_name = var_name';
    var_loc = var_loc';
    var_type = var_type';
    var_const = var_const';
    var_ghost = var_ghost';
    var_implicit = var_implicit';
  } 

  in var_decl', tbl

  and variant_decl_disambiguate (variant_decl : Type.variant_decl) tbl =
    let variant_name', tbl = new_ident_disambiguate variant_decl.variant_name tbl in (*  : ident; *)
    let variant_loc' = variant_decl.variant_loc in (*  : location; *)
    let variant_args', tbl = list_disambiguate var_decl_disambiguate variant_decl.variant_args tbl in (*  : var_decl list; *)

    let (variant_decl': Type.variant_decl) = 
    { variant_name = variant_name';
      variant_loc = variant_loc';
      variant_args = variant_args';
    }

  in variant_decl', tbl

  and type_disambiguate exp tbl = match exp with
    | Int
    | Bool
    | Unit
    | AnyRef
    | Perm
    | Bot
    | Any
    | Set
    | Map -> exp, tbl
    | Var qual_ident -> let qual_ident', tbl = qual_ident_disambiguate qual_ident tbl
      in (Var qual_ident'), tbl
    | Struct var_decl_list ->
      let var_decl_list', tbl = list_disambiguate struct_var_decl_disambiguate var_decl_list tbl in
      (Struct var_decl_list'), tbl
    | Data variant_decl_list -> let variant_decl_list', tbl = list_disambiguate variant_decl_disambiguate variant_decl_list tbl
        in (Data variant_decl_list'), tbl
    | App (tp, tp_list, tp_attr) -> 
        let tp', tbl = type_disambiguate tp tbl in
        let tp_list', tbl = list_disambiguate type_disambiguate tp_list tbl in
        let tp_attr', tbl = type_attr_disambiguate tp_attr tbl

      in (App (tp', tp_list', tp_attr')), tbl
  (*| TypeData of qual_ident * type_attr*)
    | Dot (tp, iden, tp_attr) ->
        let tp', tbl = type_disambiguate tp tbl in
        let iden', tbl = old_ident_disambiguate iden tbl in
        let tp_attr', tbl = type_attr_disambiguate tp_attr tbl

      in (Dot (tp', iden', tp_attr')), tbl
end

let type_expr_disambiguate = TypeDisambiguate.type_disambiguate
let var_decl_disambiguate = TypeDisambiguate.var_decl_disambiguate

module ExprDisambiguate = struct
  let rec constr_disambiguate (const : Expr.constr) tbl : (Expr.constr * SymbolTbl.t) = match const with
    | Null
    | Unit
    | Bool _
    | Int _
    | Empty
    | Not
    | Uminus
    | Eq
    | Gt
    | Lt
    | Geq
    | Leq
    | Diff
    | Union
    | Inter
    | Elem
    | Subseteq
    | And
    | Or
    | Impl
    | Plus
    | Minus
    | Mult
    | Div
    | Mod
    | Dot
    | Call
    | Read 
    (* Ternary operators *)
    | Ite
    | Write
    | Own
    (* Variable arity operators *)
    | Setenum -> const, tbl
    | Var qual_ident -> let qual_ident', tbl = qual_ident_disambiguate qual_ident tbl
        in (Var qual_ident'), tbl
    | New tp_expr -> let tp_expr', tbl = type_expr_disambiguate tp_expr tbl
        in (New tp_expr'), tbl

  and binder_disambiguate bind tbl = bind, tbl

  and expr_attr_disambiguate (expr_att: Expr.expr_attr) tbl = 
    let expr_loc' = expr_att.expr_loc in (* : location; *)
    let expr_type', tbl =  type_expr_disambiguate expr_att.expr_type tbl in (* : type_expr; *)

    let (expr_att': Expr.expr_attr) =
    { expr_loc = expr_loc';
      expr_type = expr_type';
    }

  in expr_att', tbl

  and expr_disambiguate (exp: expr) tbl : (expr * SymbolTbl.t) = match exp with
    | App (Read, exp_list, exp_attr) ->
        let exp_list', tbl = (match exp_list with
          | [h; t] -> let t', tbl = expr_disambiguate t tbl in [h; t'], tbl
          | _ -> raise (Failure "Read expression has an invalid number of arguments") )
        
        in

        let exp_attr', tbl = expr_attr_disambiguate exp_attr tbl in
        (App (Read, exp_list', exp_attr')), tbl
    | App (con, exp_list, exp_attr) ->
        let con', tbl = constr_disambiguate con tbl in
        let exp_list', tbl = list_disambiguate expr_disambiguate exp_list tbl in
        let exp_attr', tbl = expr_attr_disambiguate exp_attr tbl
        
        in (App (con', exp_list', exp_attr')), tbl

    | Binder (bind, var_decl_list, exp, exp_attr) ->
        let bind', tbl = binder_disambiguate bind tbl in
        let var_decl_list', tbl = list_disambiguate var_decl_disambiguate var_decl_list tbl in
        let exp', tbl = expr_disambiguate exp tbl in
        let exp_attr', tbl = expr_attr_disambiguate exp_attr tbl

        in (Binder (bind', var_decl_list', exp', exp_attr')), tbl

end

let expr_disambiguate = ExprDisambiguate.expr_disambiguate

module StmtDisambiguate = struct
  let rec spec_disambiguate (spec: Stmt.spec) tbl = 
    (* TODO: REVISIT THIS *)
    let spec_form', tbl = expr_disambiguate spec.spec_form tbl in       (* : expr *)
    let spec_atomic' = spec.spec_atomic in      (* : bool *)
    let spec_name' = spec.spec_name in      (* : string *)
    let spec_error' = spec.spec_error in      (* : (qual_ident -> (string * string)) option *)

    let (spec': Stmt.spec) =
    { spec_form = spec_form';
      spec_atomic = spec_atomic';
      spec_name = spec_name';
      spec_error = spec_error';
    }

    in spec', tbl

  and var_def_disambiguate (var_def: Stmt.var_def) tbl =
    let var_decl', tbl = var_decl_disambiguate var_def.var_decl tbl in (*  : var_decl; *)
    let var_init', tbl = option_disambiguate expr_disambiguate var_def.var_init tbl in (*  : expr option; *)
  
    let (var_def': Stmt.var_def) = 
    { var_decl = var_decl';
      var_init = var_init';
    }

  in var_def', tbl

  and new_desc_disambiguate (new_desc: Stmt.new_desc) tbl =
    let new_lhs', tbl = new_ident_disambiguate new_desc.new_lhs tbl in (* : ident; *)
    let new_type', tbl = type_expr_disambiguate new_desc.new_type tbl in (* : type_expr; *)
    let new_args', tbl = list_disambiguate expr_disambiguate new_desc.new_args tbl in (* : expr list; *)
    
    let (new_desc': Stmt.new_desc) =
    { new_lhs = new_lhs';
      new_type = new_type';
      new_args = new_args';
    }

  in new_desc', tbl

  and assign_desc_disambiguate (assign_desc: Stmt.assign_desc) tbl =
    let assign_lhs', tbl = list_disambiguate expr_disambiguate assign_desc.assign_lhs tbl in (*  : expr list; *)
    let assign_rhs', tbl = expr_disambiguate assign_desc.assign_rhs tbl in (*  : expr; *)

    let (assign_desc': Stmt.assign_desc) = 
    { assign_lhs = assign_lhs';
      assign_rhs = assign_rhs';
    }

  in assign_desc', tbl
  
  and call_desc_disambiguate (call_desc: Stmt.call_desc) tbl = 
    let call_lhs', tbl = list_disambiguate qual_ident_disambiguate call_desc.call_lhs tbl in (*  : qual_ident list; *)
    let call_name', tbl = qual_ident_disambiguate call_desc.call_name tbl in (*  : qual_ident; *)
    let call_args', tbl = list_disambiguate expr_disambiguate call_desc.call_args tbl in (*  : expr list; *)

    let (call_desc': Stmt.call_desc) =
    { call_lhs = call_lhs';
      call_name = call_name';
      call_args = call_args';
    }

  in call_desc', tbl

  and fold_desc_disambiguate (fold_desc: Stmt.fold_desc) tbl = 
    let fold_expr', tbl = expr_disambiguate fold_desc.fold_expr tbl in (* : expr; *)

    let (fold_desc': Stmt.fold_desc) = 
    { fold_expr = fold_expr';
    }
  
  in fold_desc', tbl

  and unfold_desc_disambiguate (unfold_desc: Stmt.unfold_desc) tbl =
    let unfold_expr', tbl = expr_disambiguate unfold_desc.unfold_expr tbl in

    let (unfold_desc': Stmt.unfold_desc) =
    { unfold_expr = unfold_expr';
    }

  in unfold_desc', tbl

  and basic_stmt_desc_disambiguate (basic_stmt: Stmt.basic_stmt_desc) tbl : (Stmt.basic_stmt_desc * (SymbolTbl.t * var_decl list)) = match basic_stmt with
    | VarDef var_def -> let var_def', tbl = var_def_disambiguate var_def tbl
        in (VarDef var_def'), (tbl, [var_def'.var_decl])
    | Assume spec -> let spec', tbl = spec_disambiguate spec tbl
        in (Assume spec'), (tbl, [])
    | Assert spec -> let spec', tbl = spec_disambiguate spec tbl
        in (Assert spec'), (tbl, [])
    | New new_desc -> let new_desc', tbl = new_desc_disambiguate new_desc tbl
        in (New new_desc'), (tbl, [])
    | Assign assign_desc -> let assign_desc', tbl = assign_desc_disambiguate assign_desc tbl
        in (Assign assign_desc'), (tbl, [])
    | Havoc expr_list -> let expr_list', tbl = list_disambiguate expr_disambiguate expr_list tbl
        in (Havoc expr_list'), (tbl, [])
    | Call call_desc -> let call_desc', tbl = call_desc_disambiguate call_desc tbl
        in (Call call_desc'), (tbl, [])
    | Return expr_list -> let expr_list', tbl = list_disambiguate expr_disambiguate expr_list tbl
        in (Return expr_list'), (tbl, [])
    | Fold fold_desc -> let fold_desc', tbl = fold_desc_disambiguate fold_desc tbl
        in (Fold fold_desc'), (tbl, [])
    | Unfold unfold_desc -> let unfold_desc', tbl = unfold_desc_disambiguate unfold_desc tbl
        in (Unfold unfold_desc'), (tbl, [])

  and stmt_disambiguate (stmt: Stmt.t) (tbl, locals) =
    let stmt_desc', (tbl, locals) = stmt_desc_disambiguate stmt.stmt_desc (tbl, locals) in (*  stmt_desc; *)
    let stmt_loc' = stmt.stmt_loc in (*  location; *)

    let (stmt': Stmt.t) =
    { stmt_desc = stmt_desc';
      stmt_loc = stmt_loc';
    }

  in stmt', (tbl, locals)

  and loop_desc_disambiguate (loop_desc: Stmt.loop_desc) (tbl, locals)(* : SymbolTbl.t * var_decl list *) =
    let tbl = SymbolTbl.push tbl in 
    let loop_contract', tbl = list_disambiguate spec_disambiguate loop_desc.loop_contract tbl in  (* : spec list; *)
    let loop_prebody', (tbl, locals) = stmt_disambiguate loop_desc.loop_prebody (tbl, locals) in  (* : t; *)
    let loop_test', tbl = expr_disambiguate loop_desc.loop_test tbl in  (* : expr; *)
    let loop_postbody', (tbl, locals) = stmt_disambiguate loop_desc.loop_postbody (tbl, locals) in  (* : t; *)
    let tbl = SymbolTbl.pop tbl in

    let (loop_desc': Stmt.loop_desc) = 
    { loop_contract = loop_contract';
      loop_prebody = loop_prebody';
      loop_test = loop_test';
      loop_postbody = loop_postbody';
    }

  in loop_desc', (tbl, locals)

  and cond_desc_disambiguate (cond_desc: Stmt.cond_desc) (tbl, locals) =
    let cond_test', tbl = expr_disambiguate cond_desc.cond_test tbl in (* : expr; *)
    let tbl = SymbolTbl.push tbl in
    let cond_then', (tbl, locals) = stmt_disambiguate cond_desc.cond_then (tbl, locals) in (* : t; *)
    let tbl = SymbolTbl.pop tbl in
    let tbl = SymbolTbl.push tbl in
    let cond_else', (tbl, locals) = stmt_disambiguate cond_desc.cond_else (tbl, locals) in (* : t; *)
    let tbl = SymbolTbl.pop tbl in

    let (cond_desc': Stmt.cond_desc) = 
    { cond_test = cond_test';
      cond_then = cond_then';
      cond_else = cond_else';
    }

  in cond_desc', (tbl, locals)

  and ghost_desc_disambiguate (ghost_desc: Stmt.ghost_desc) (tbl, locals) =
    let tbl = SymbolTbl.push tbl in
    let ghost_body', (tbl, locals) = list_disambiguate stmt_disambiguate ghost_desc.ghost_body (tbl, locals) in (* : t list; *)
    let tbl = SymbolTbl.pop tbl in

    let (ghost_desc': Stmt.ghost_desc) = 
    { ghost_body = ghost_body';
    }

    in ghost_desc', (tbl, locals)

  and stmt_desc_disambiguate stmt_desc (tbl, locals) = match stmt_desc with
    | Block stmt_list -> 
        let tbl = SymbolTbl.push tbl in  
        let stmt_list', (tbl, locals) = list_disambiguate stmt_disambiguate stmt_list (tbl, locals) in
        let tbl = SymbolTbl.pop tbl
      in (Block stmt_list'), (tbl, locals)
    | Basic basic_stmt_desc -> let basic_stmt_desc', (tbl, locals') = basic_stmt_desc_disambiguate basic_stmt_desc tbl
      in (Basic basic_stmt_desc'), (tbl, List.append locals locals')
    | Loop loop_desc -> let loop_desc', (tbl, locals) = loop_desc_disambiguate loop_desc (tbl, locals)
      in (Loop loop_desc'), (tbl, locals)
    | Cond cond_desc -> let cond_desc', (tbl, locals) = cond_desc_disambiguate cond_desc (tbl, locals)
      in (Cond cond_desc'), (tbl, locals)
    | Ghost ghost_desc -> let ghost_desc', (tbl, locals) = ghost_desc_disambiguate ghost_desc (tbl, locals)
      in (Ghost ghost_desc'), (tbl, locals)
end

let stmt_disambiguate = StmtDisambiguate.stmt_disambiguate

module CallableDisambiguate = struct
  let rec locals_to_string (m: ((ident * Type.var_decl) list)) = match m with
    | [] -> ""
    | l::ls -> Ident.to_string (fst l) ^ " -> " ^ Ident.to_string (snd l).var_name ^ ",   " ^(locals_to_string ls)
    

  let rec call_decl_disambiguate (call_decl: Callable.call_decl) tbl = 
    let call_decl_kind' = call_decl.call_decl_kind in
    let call_decl_name', tbl = new_ident_disambiguate call_decl.call_decl_name tbl in
    let tbl = SymbolTbl.push tbl in
    (* Corresponding SymbolTbl.pop made in proc_def_disambiguate and func_def_disambiguate *)
    let call_decl_locals', tbl = ident_map_old_disambiguate var_decl_disambiguate call_decl.call_decl_locals tbl in
    let call_decl_formals', tbl = list_disambiguate old_ident_disambiguate call_decl.call_decl_formals tbl in
    let call_decl_returns', tbl = list_disambiguate old_ident_disambiguate call_decl.call_decl_returns tbl in
    let call_decl_precond', tbl = list_disambiguate StmtDisambiguate.spec_disambiguate call_decl.call_decl_precond tbl in
    let call_decl_postcond', tbl = list_disambiguate StmtDisambiguate.spec_disambiguate call_decl.call_decl_postcond tbl in
    let call_decl_loc' = call_decl.call_decl_loc in

    let (call_decl': Callable.call_decl) = 
    { call_decl_kind = call_decl_kind';
      call_decl_name = call_decl_name';
      call_decl_formals = call_decl_formals';
      call_decl_returns = call_decl_returns';
      call_decl_locals = call_decl_locals';
      call_decl_precond = call_decl_precond';
      call_decl_postcond = call_decl_postcond';
      call_decl_loc = call_decl_loc';
    }

  in call_decl', tbl
  
  and proc_def_disambiguate (proc_def: Callable.proc_def) tbl =
    let rec map_append m (l: var_decl list) = match l with 
      | [] -> m
      | v::vs -> map_append (Map.add_exn m ~key:v.var_name ~data:v) vs
    
    in

    let proc_decl', tbl = call_decl_disambiguate proc_def.proc_decl tbl in
    let proc_body', (tbl, locals) = option_disambiguate stmt_disambiguate proc_def.proc_body (tbl, []) in
    
    let tbl = SymbolTbl.pop tbl in 

    let proc_decl'' = {proc_decl' with call_decl_locals = map_append proc_decl'.call_decl_locals locals;} in 

    print_debug ("LOCALS OUTPUT: " ^ locals_to_string (Map.to_alist proc_decl''.call_decl_locals) ^ "\n\n");
    (* Corresponding push made in call_decl_disambiguate *)
    let (proc_def': Callable.proc_def) =
    { proc_decl = proc_decl''; 
      proc_body = proc_body';
    }

  in proc_def', tbl

  and func_def_disambiguate (func_def: Callable.func_def) tbl =
    let func_decl', tbl = call_decl_disambiguate func_def.func_decl tbl in
    let func_body', tbl = option_disambiguate expr_disambiguate func_def.func_body tbl in
    let tbl = SymbolTbl.pop tbl in
    (* Corresponding push made in call_decl_disambiguate *)

    let (func_def': Callable.func_def) =
    { func_decl = func_decl'; 
      func_body = func_body';
    }

  in func_def', tbl

  and callable_disambiguate (call: Callable.t) tbl : (Callable.t * SymbolTbl.t) = match call with
    | FuncDef func_def -> let func_def', tbl = func_def_disambiguate func_def tbl 
        in (FuncDef func_def'), tbl
    | ProcDef proc_def -> let proc_def', tbl = proc_def_disambiguate proc_def tbl
        in (ProcDef proc_def'), tbl

end

let callable_disambiguate = CallableDisambiguate.callable_disambiguate

module ModuleDisambiguate = struct
  let rec type_alias_disambiguate (type_alias: Module.type_alias) tbl = 
    let type_alias_name', tbl = new_ident_disambiguate type_alias.type_alias_name tbl in
    let type_alias_def', tbl = option_disambiguate type_expr_disambiguate type_alias.type_alias_def tbl in
    let type_alias_rep' = type_alias.type_alias_rep in
    let type_alias_loc' = type_alias.type_alias_loc in
  
    let (type_alias': Module.type_alias) =
    { type_alias_name = type_alias_name';
      type_alias_def = type_alias_def';
      type_alias_rep = type_alias_rep';
      type_alias_loc = type_alias_loc';
    }

  in type_alias', tbl

  and mod_alias_disambiguate (mod_alias: Module.module_alias) tbl = 
    let mod_alias_name', tbl = new_ident_disambiguate mod_alias.mod_alias_name tbl in
    let mod_alias_type', tbl = type_expr_disambiguate mod_alias.mod_alias_type tbl in
    let mod_alias_def', tbl = option_disambiguate type_expr_disambiguate mod_alias.mod_alias_def tbl in
    let mod_alias_loc' = mod_alias.mod_alias_loc in
    
    let (mod_alias': Module.module_alias) = 
    { mod_alias_name = mod_alias_name';
      mod_alias_type = mod_alias_type';
      mod_alias_def = mod_alias_def';
      mod_alias_loc = mod_alias_loc';
    }

  in mod_alias', tbl

(* 
and mod_decl_disambiguate (mod_decl: Module.module_decl) tbl =
    let mod_decl_name', tbl = (* new_ident_disambiguate *) mod_decl.mod_decl_name, tbl in
    (* Not new_ident-ing module names. Assuming module names are unique, probably want to revisit. *)
    let mod_decl_formals', tbl = list_disambiguate new_ident_disambiguate mod_decl.mod_decl_formals tbl in
    let mod_decl_returns', tbl = list_disambiguate type_expr_disambiguate mod_decl.mod_decl_returns tbl in
    let mod_decl_rep', tbl = option_disambiguate old_ident_disambiguate mod_decl.mod_decl_rep tbl in
    print_debug ("MODULE : " ^ Ident.to_string mod_decl_name' ^ " -> " ^ (match mod_decl_rep' with | None -> "None" | Some rep -> Ident.to_string rep) ^ "\n");
    let tbl = match tbl with
    | []
    | _ :: [] -> tbl
    | t :: ts -> match mod_decl_rep' with
        | None -> (t :: ts)
        | Some rep -> print_debug ("REP TYPE Adding: " ^ Ident.to_string mod_decl_name' ^ " -> " ^ Ident.to_string rep);
          t :: (SymbolTbl.add ts (QualIdent.from_ident mod_decl_name') (QualIdent.make [mod_decl_name'] rep)) in

    let mod_decl_mod_defs', tbl = ident_map_new_disambiguate mod_decl_disambiguate mod_decl.mod_decl_mod_defs tbl in
    let mod_decl_mod_aliases', tbl = ident_map_new_disambiguate mod_alias_disambiguate mod_decl.mod_decl_mod_aliases tbl in
    let mod_decl_types', tbl = ident_map_new_disambiguate type_alias_disambiguate mod_decl.mod_decl_types tbl in
    let mod_decl_callables', tbl = ident_map_new_disambiguate CallableDisambiguate.call_decl_disambiguate mod_decl.mod_decl_callables tbl in
    let mod_decl_vars', tbl =  ident_map_new_disambiguate var_decl_disambiguate mod_decl.mod_decl_vars tbl in
    let mod_decl_loc' = mod_decl.mod_decl_loc in

    let (mod_decl': Module.module_decl) = 
    { mod_decl_name = mod_decl_name';
      mod_decl_formals = mod_decl_formals';
      mod_decl_returns = mod_decl_returns';
      mod_decl_rep = mod_decl_rep';
      mod_decl_mod_defs = mod_decl_mod_defs';
      mod_decl_mod_aliases = mod_decl_mod_aliases';
      mod_decl_types = mod_decl_types';
      mod_decl_callables = mod_decl_callables';
      mod_decl_vars = mod_decl_vars';
      mod_decl_loc = mod_decl_loc';
    }

  in mod_decl', tbl *)
  
  and import_directive_disambiguate (imp_dir: Module.import_directive) tbl : (Module.import_directive * SymbolTbl.t) = match imp_dir with
    | ModImport tp_exp -> let tp_exp', tbl = type_expr_disambiguate tp_exp tbl in
        (ModImport tp_exp'), tbl
    | MemImport qual_id -> let qual_id', tbl = qual_ident_disambiguate qual_id tbl in
        (MemImport qual_id'), tbl
  
  and member_def_disambiguate (mem_def: Module.member_def) tbl : (Module.member_def * SymbolTbl.t) = match mem_def with
    | TypeAlias tp_alias -> let tp_alias', tbl = type_alias_disambiguate tp_alias tbl in
        (TypeAlias tp_alias'), tbl
    | Import imp_dir -> let imp_dir', tbl = import_directive_disambiguate imp_dir tbl in
        (Import imp_dir'), tbl
    | ModDef mod_def -> let mod_def', tbl = mod_def_disambiguate mod_def tbl in
        (ModDef mod_def'), tbl
    | ValDef var_defn -> let var_defn', tbl = StmtDisambiguate.var_def_disambiguate var_defn tbl in
        (ValDef var_defn'), tbl
    | CallDef call -> let call', tbl = callable_disambiguate call tbl in
        (CallDef call'), tbl

  and mod_def_disambiguate mod_def tbl = match mod_def with
    | ModImpl mod1 -> let mod', tbl = module_disambiguate mod1 tbl in
        ((ModImpl mod'), tbl)
    | ModAlias mod_alias -> let mod_alias', tbl = mod_alias_disambiguate mod_alias tbl in
        ((ModAlias mod_alias'), tbl)
    
  and module_disambiguate mod1 tbl =
    let rec extract_members (mod_defs_list: Module.member_def list) (rep, mod_defs, mod_aliases, types, callables, vars) = 
      match mod_defs_list with 
      | [] -> (rep, mod_defs, mod_aliases, types, callables, vars)
      | def :: defs -> match def with
          | TypeAlias type_alias ->
              let rep =  if (type_alias.type_alias_rep) then (Some type_alias.type_alias_name) else rep in
              let types = (Map.add_exn types ~key:type_alias.type_alias_name ~data:type_alias) in
              extract_members defs (rep, mod_defs, mod_aliases, types, callables, vars)
          | Import _ -> 
              extract_members defs (rep, mod_defs, mod_aliases, types, callables, vars)
          | ModDef module_def -> (match module_def with 
              | ModImpl mod_impl -> let mod_defs = Map.add_exn mod_defs ~key:mod_impl.mod_decl.mod_decl_name ~data:mod_impl.mod_decl in
              extract_members defs (rep, mod_defs, mod_aliases, types, callables, vars)
              | ModAlias mod_alias -> let mod_aliases = Map.add_exn mod_aliases ~key:mod_alias.mod_alias_name ~data: mod_alias in
              extract_members defs (rep, mod_defs, mod_aliases, types, callables, vars) )
          | ValDef v -> let vars = Map.add_exn vars ~key:v.var_decl.var_name ~data:v.var_decl in
              extract_members defs (rep, mod_defs, mod_aliases, types, callables, vars)
          | CallDef call -> let cl_decl = (match call with
              | FuncDef fn -> fn.func_decl
              | ProcDef proc -> proc.proc_decl) in
              
              let callables = Map.add_exn callables ~key:cl_decl.call_decl_name ~data:cl_decl in
              extract_members defs (rep, mod_defs, mod_aliases, types, callables, vars)

      in

    let mod_decl_name' = mod1.mod_decl.mod_decl_name in

    let tbl = SymbolTbl.push_name mod_decl_name' tbl in
    let mod_def', tbl = list_disambiguate member_def_disambiguate mod1.mod_def tbl in
    let (rep, mod_defs, mod_aliases, types, callables, vars) = extract_members mod_def' (mod1.mod_decl.mod_decl_rep, mod1.mod_decl.mod_decl_mod_defs, mod1.mod_decl.mod_decl_mod_aliases, mod1.mod_decl.mod_decl_types, mod1.mod_decl.mod_decl_callables, mod1.mod_decl.mod_decl_vars) in
    
    let tbl = match tbl with
    | []
    | _ :: [] -> tbl
    | t :: ts -> match rep with
        | None -> (t :: ts)
        | Some r -> print_debug ("REP TYPE Adding: " ^ Ident.to_string mod_decl_name' ^ " -> " ^ Ident.to_string r);
          t :: (SymbolTbl.add ts (QualIdent.from_ident mod_decl_name') (QualIdent.make [mod_decl_name'] r)) 
        
    in

    let (mod_decl': Module.module_decl) = 
    { mod_decl_name = mod_decl_name';
      mod_decl_formals = mod1.mod_decl.mod_decl_formals;
      mod_decl_returns = mod1.mod_decl.mod_decl_returns;
      mod_decl_rep = rep;
      mod_decl_mod_defs = mod_defs;
      mod_decl_mod_aliases = mod_aliases;
      mod_decl_types = types;
      mod_decl_callables = callables;
      mod_decl_vars = vars;
      mod_decl_loc = mod1.mod_decl.mod_decl_loc;
    }

    in

    let mod_interface' = mod1.mod_interface in
    let tbl = SymbolTbl.pop tbl in

    let (mod': Module.t) = 
    { mod_decl = mod_decl';
      mod_def = mod_def';
      mod_interface = mod_interface';
    }

  in mod', tbl
end

let module_disambiguate = ModuleDisambiguate.module_disambiguate


let start_disambiguate m = module_disambiguate m (SymbolTbl.push [])
