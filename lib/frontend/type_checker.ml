(** Checks and assigns types to all expressions *)
open Base
open Ast 
(* open Util *)

module SymbolTbl = struct
(*   module IdentMap = Map.M(Ident)
  type 'a ident_map = 'a IdentMap.t *)

  type type_qual_ident_map = type_expr qual_ident_map

  (* type t = (ident ident_map) list *)

  type t = (ident option * type_qual_ident_map) list

  let label_to_string label = match label with
  | None -> "__"
  | Some iden -> Ident.to_string iden

  let rec map_to_string t = match t with
  | [] -> " "
  | (k,v) :: ms -> (QualIdent.to_string k ^ " -> " ^ Type.to_string v ^ "\n") ^ (map_to_string ms)

  let rec to_string tbl = match tbl with
    | [] -> "end\n\n"
    | t :: ts -> label_to_string (fst t) ^ " :: [ " ^ map_to_string (Map.to_alist (snd t)) ^ " ]\n" ^ (to_string ts)

  let push ?(name = None) tbl : t = (name, Map.empty (module QualIdent)) :: tbl

  let push_name name tbl = push ~name:(Some name) tbl

  let pop tbl = match tbl with
  | [] -> raise(Failure "Empty symbol table")
  | _ :: ts -> ts

(* 
  let rec fully_qualified (id: qual_ident) tbl = match tbl with
    | [] -> id
    | (label, _) :: ts -> match label with
        | None -> id
        | Some iden -> fully_qualified (QualIdent.left_append iden id) ts

 *)
  let rec add_helper tbl name tp =
    match tbl with
    | [] -> []
    | t :: ts -> let (label, map) = t in
          let t' = 
            try
              (label, (Map.add_exn (map) ~key:name ~data:tp)) 
            with _ -> raise(Failure ("duplicate exists: " ^ QualIdent.to_string name ^ " to " ^ Type.to_string tp))
          in
          let ts' = match label with
              | None -> ts
              | Some iden -> add_helper ts (QualIdent.left_append iden name) tp

          in
          t' :: ts'

  let add tbl name tp = 
    print_debug ("ADDING " ^ QualIdent.to_string name ^ " -> " ^ Type.to_string tp ^ "\n" ^ to_string tbl);
  match tbl with
    | [] -> raise(Failure "Empty symbol table")
    | tbl -> add_helper tbl name tp

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

let option_type_check fn arg tbl = match arg with
  | None -> None, tbl
  | Some s -> let s', tbl = fn s tbl in
      (Some s'), tbl

let rec list_type_check fn arg tbl = match arg with
  | [] -> [], tbl
  | l :: ls -> let l', tbl = fn l tbl in
      let ls', tbl = list_type_check fn ls tbl 
        in ((l' :: ls'), tbl)

(* module IdentTypeCheck = struct
  let old_ident_type_check iden (tbl: SymbolTbl.t) = print_debug ("Old_Ident: " ^ Ident.to_string iden ^ "\n");
    match (SymbolTbl.find tbl (QualIdent.from_ident iden)) with
    | None -> raise(Failure ("Variable Not Ref: " ^ Ident.to_string iden))
    | Some id -> id.qual_base, tbl
  
  let new_ident_type_check iden (tbl: SymbolTbl.t) = print_debug ("New_Ident: " ^ Ident.to_string iden ^ "\n");
    let iden' = Ident.fresh iden.ident_name in
    let tbl = SymbolTbl.add tbl (QualIdent.from_ident iden) (QualIdent.from_ident iden') in
    iden', tbl

end

let old_ident_type_check = IdentTypeCheck.old_ident_type_check
let new_ident_type_check = IdentTypeCheck.new_ident_type_check *)

let ident_map_type_check val_fun id_map tbl = 
  let rec fn_iter l tbl = match l with
    | [] -> [], tbl
    | (id, value) :: ls -> 
        let value', tbl = val_fun value tbl in
        let ls', tbl = fn_iter ls tbl in
          ((id, value') :: ls'), tbl

  in let l', tbl = fn_iter (Map.to_alist id_map) tbl
in (Map.of_alist_exn (module Ident) l'), tbl

(* let ident_map_type_check val_fun id_map tbl = 
  let fn (id, value) tbl =
    let value', tbl = val_fun value tbl in
    let id', tbl = old_ident_type_check id tbl in
    (id', value'), tbl

  in
  let rec fn_iter l tbl = match l with
    | [] -> [], tbl
    | (id, value) :: ls -> 
        let (id', value'), tbl = fn (id, value) tbl in
        let ls', tbl = fn_iter ls tbl in
          ((id', value') :: ls'), tbl

  in let l', tbl = fn_iter (Map.to_alist id_map) tbl
in (Map.of_alist_exn (module Ident) l'), tbl *)

(* module QualIdentTypeCheck = struct
  let rec qual_ident_type_check (qual_iden : qual_ident) tbl =
    print_debug ("Old_QualIdent: " ^ QualIdent.to_string qual_iden ^ "\n");
    match (SymbolTbl.find tbl qual_iden) with
    | None -> raise(Failure ("Variable Not Ref: " ^ QualIdent.to_string qual_iden))
    | Some tp -> id, tbl
end

let qual_ident_type_check = QualIdentTypeCheck.qual_ident_type_check *)

module TypeTypeCheck = struct
  let rec type_attr_type_check tp_attr tbl = tp_attr, tbl

  and var_decl_type_check (var_decl : Type.var_decl) tbl =
    let tbl = SymbolTbl.add tbl (QualIdent.from_ident var_decl.var_name) var_decl.var_type

    (* let var_name' = var_decl.var_name in
    let var_loc' = var_decl.var_loc in
    let var_type', tbl = var_decl.var_type, tbl in
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
 *)
  in var_decl, tbl

  and variant_decl_type_check (variant_decl : Type.variant_decl) tbl =
    let variant_name' = variant_decl.variant_name in (*  : ident; *)
    let variant_loc' = variant_decl.variant_loc in (*  : location; *)
    let variant_args', tbl = list_type_check var_decl_type_check variant_decl.variant_args tbl in (*  : var_decl list; *)

    let (variant_decl': Type.variant_decl) = 
    { variant_name = variant_name';
      variant_loc = variant_loc';
      variant_args = variant_args';
    }

  in variant_decl', tbl

(*   and type_type_check exp tbl = match exp with
    | Int
    | Bool
    | Unit
    | AnyRef
    | Perm
    | Bot
    | Any
    | Set
    | Map -> exp, tbl
    | Var qual_ident -> let qual_ident', tbl = qual_ident_type_check qual_ident tbl
      in (Var qual_ident'), tbl
    | Struct var_decl_list ->
      let var_decl_list', tbl = list_type_check var_decl_type_check var_decl_list tbl in
      (Struct var_decl_list'), tbl
    | Data variant_decl_list -> let variant_decl_list', tbl = list_type_check variant_decl_type_check variant_decl_list tbl
        in (Data variant_decl_list'), tbl
    | App (tp, tp_list, tp_attr) -> 
        let tp', tbl = type_type_check tp tbl in
        let tp_list', tbl = list_type_check type_type_check tp_list tbl in
        let tp_attr', tbl = type_attr_type_check tp_attr tbl

      in (App (tp', tp_list', tp_attr')), tbl
  (*| TypeData of qual_ident * type_attr*)
    | Dot (tp, iden, tp_attr) ->
        let tp', tbl = type_type_check tp tbl in
        let iden', tbl = old_ident_type_check iden tbl in
        let tp_attr', tbl = type_attr_type_check tp_attr tbl

      in (Dot (tp', iden', tp_attr')), tbl *)
end

(* let type_expr_type_check = TypeTypeCheck.type_type_check *)
let var_decl_type_check = TypeTypeCheck.var_decl_type_check

module ExprTypeCheck = struct
(*   let rec constr_type_check (const : Expr.constr) tbl : (Expr.constr * SymbolTbl.t) = match const with
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
    | Setenum
    | Var _ (* qual_ident -> let qual_ident', tbl = qual_ident_type_check qual_ident tbl
        in (Var qual_ident'), tbl *)
    | New _ -> const, tbl(* tp_expr -> let tp_expr', tbl = type_expr_type_check tp_expr tbl
        in (New tp_expr'), tbl *) *)

  (* and binder_type_check bind tbl = bind, tbl *)

(*   and expr_attr_type_check (expr_att: Expr.expr_attr) tbl = 
    let expr_loc' = expr_att.expr_loc in (* : location; *)
    let expr_type', tbl =  type_expr_type_check expr_att.expr_type tbl in (* : type_expr; *)

    let (expr_att': Expr.expr_attr) =
    { expr_loc = expr_loc';
      expr_type = expr_type';
    }

  in expr_att', tbl *)

    let type_of_expr (exp: Expr.t) = match exp with
      | App (_, _, exp_attr) -> exp_attr.expr_type
      | Binder (_, _, _, exp_attr) -> exp_attr.expr_type

  let rec expr_type_check (exp: expr) tbl : (expr * SymbolTbl.t) = match exp with
    | App (con, exp_list, exp_attr) ->
        let exp_list', tbl = list_type_check expr_type_check exp_list tbl in
        let exp_attr' = { exp_attr with expr_type = (match con with
          | Null 
          | Unit -> Any
          | Bool _ -> Bool
          | Int _ -> Int
          | Empty -> Set
          | Not -> Bool
          | Uminus -> Int
          | Eq -> (match exp_list' with 
            | [] -> Any
            | h :: _ -> type_of_expr h)
          | Gt
          | Lt
          | Geq
          | Leq -> Bool
          | Diff
          | Union
          | Inter
          | Elem
          | Subseteq -> Set
          | And
          | Or
          | Impl -> Bool
          | Plus
          | Minus
          | Mult
          | Div
          | Mod -> Int
          | Dot 
          | Call
          | Read 
          (* Ternary operators *)
          | Ite
          | Write -> Any
          | Own -> Any
          (* Variable arity operators *)
          | Setenum -> Set
          | Var qual_iden -> (match SymbolTbl.find tbl qual_iden with
              | None -> raise(Failure ("Type of `" ^ QualIdent.to_string qual_iden ^ "` not found."))
              | Some t -> t)
          | New t -> t
            ) }

        in (App (con, exp_list', exp_attr')), tbl

    | Binder (bind, var_decl_list, exp, exp_attr) ->
        let var_decl_list', tbl = list_type_check var_decl_type_check var_decl_list tbl in 
        (* var_decl_type_check adds the types of var_decls to SymbolTbl *)
        let exp', tbl = expr_type_check exp tbl in
        let exp_attr' = { exp_attr with expr_type = type_of_expr exp'; }

        in (Binder (bind, var_decl_list', exp', exp_attr')), tbl

end

let expr_type_check = ExprTypeCheck.expr_type_check
let type_of_expr = ExprTypeCheck.type_of_expr

module StmtTypeCheck = struct
  let rec spec_type_check (spec: Stmt.spec) tbl = 
    let spec_form', tbl = expr_type_check spec.spec_form tbl in       (* : expr *)
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

  and var_def_type_check (var_def: Stmt.var_def) tbl =
    let var_init', tbl = option_type_check expr_type_check var_def.var_init tbl in (*  : expr option; *)
    let tp = (match var_init' with 
      | None -> var_def.var_decl.var_type
      | Some e -> type_of_expr e) in
    
    let var_decl' = { var_def.var_decl with var_type = tp } in
    let var_decl'', tbl = var_decl_type_check var_decl' tbl in (*  : var_decl; *)
    
  
    let (var_def': Stmt.var_def) = 
    { var_decl = var_decl'';
      var_init = var_init';
    }

  in var_def', tbl

  and new_desc_type_check (new_desc: Stmt.new_desc) tbl =
    let new_args', tbl = list_type_check expr_type_check new_desc.new_args tbl in (* : expr list; *)
    let new_lhs' = new_desc.new_lhs in (* : ident; *)
    let new_type' = new_desc.new_type in (* : type_expr; *)
    (* Todo: Need to make sure new_type' is compatible with new_args' *)

    let tbl = SymbolTbl.add tbl (QualIdent.from_ident new_lhs') new_type' in
    
    let (new_desc': Stmt.new_desc) =
    { new_lhs = new_lhs';
      new_type = new_type';
      new_args = new_args';
    }

  in new_desc', tbl

  and assign_desc_type_check (assign_desc: Stmt.assign_desc) tbl =
    let assign_lhs', tbl = list_type_check expr_type_check assign_desc.assign_lhs tbl in (*  : expr list; *)
    let assign_rhs', tbl = expr_type_check assign_desc.assign_rhs tbl in (*  : expr; *)

    (* Todo: Figure out what to do with this, unify etc. *)

    let (assign_desc': Stmt.assign_desc) = 
    { assign_lhs = assign_lhs';
      assign_rhs = assign_rhs';
    }

  in assign_desc', tbl
  
  and call_desc_type_check (call_desc: Stmt.call_desc) tbl = 
    (* Todo: Figure out what to do here. *)
    let call_lhs', tbl = (* list_type_check qual_ident_type_check *) call_desc.call_lhs, tbl in (*  : qual_ident list; *)
    let call_name', tbl = (* qual_ident_type_check *) call_desc.call_name, tbl in (*  : qual_ident; *)
    let call_args', tbl = list_type_check expr_type_check call_desc.call_args tbl in (*  : expr list; *)

    let (call_desc': Stmt.call_desc) =
    { call_lhs = call_lhs';
      call_name = call_name';
      call_args = call_args';
    }

  in call_desc', tbl

  and fold_desc_type_check (fold_desc: Stmt.fold_desc) tbl = 
    let fold_expr', tbl = expr_type_check fold_desc.fold_expr tbl in (* : expr; *)

    let (fold_desc': Stmt.fold_desc) = 
    { fold_expr = fold_expr';
    }
  
  in fold_desc', tbl

  and unfold_desc_type_check (unfold_desc: Stmt.unfold_desc) tbl =
    let unfold_expr', tbl = expr_type_check unfold_desc.unfold_expr tbl in

    let (unfold_desc': Stmt.unfold_desc) =
    { unfold_expr = unfold_expr';
    }

  in unfold_desc', tbl

  and basic_stmt_desc_type_check (basic_stmt: Stmt.basic_stmt_desc) tbl : (Stmt.basic_stmt_desc * SymbolTbl.t) = match basic_stmt with
    | VarDef var_def -> let var_def', tbl = var_def_type_check var_def tbl
        in (VarDef var_def'), tbl
    | Assume spec -> let spec', tbl = spec_type_check spec tbl
        in (Assume spec'), tbl
    | Assert spec -> let spec', tbl = spec_type_check spec tbl
        in (Assert spec'), tbl
    | New new_desc -> let new_desc', tbl = new_desc_type_check new_desc tbl
        in (New new_desc'), tbl
    | Assign assign_desc -> let assign_desc', tbl = assign_desc_type_check assign_desc tbl
        in (Assign assign_desc'), tbl
    | Havoc expr_list -> let expr_list', tbl = list_type_check expr_type_check expr_list tbl
        in (Havoc expr_list'), tbl
    | Call call_desc -> let call_desc', tbl = call_desc_type_check call_desc tbl
        in (Call call_desc'), tbl
    | Return expr_list -> let expr_list', tbl = list_type_check expr_type_check expr_list tbl
        in (Return expr_list'), tbl
    | Fold fold_desc -> let fold_desc', tbl = fold_desc_type_check fold_desc tbl
        in (Fold fold_desc'), tbl
    | Unfold unfold_desc -> let unfold_desc', tbl = unfold_desc_type_check unfold_desc tbl
        in (Unfold unfold_desc'), tbl

  and stmt_type_check (stmt: Stmt.t) tbl =
    let stmt_desc', tbl = stmt_desc_type_check stmt.stmt_desc tbl in (*  stmt_desc; *)
    let stmt_loc' = stmt.stmt_loc in (*  location; *)

    let (stmt': Stmt.t) =
    { stmt_desc = stmt_desc';
      stmt_loc = stmt_loc';
    }

  in stmt', tbl

  and loop_desc_type_check (loop_desc: Stmt.loop_desc) tbl(* : SymbolTbl.t * var_decl list *) =
    let tbl = SymbolTbl.push tbl in 
    let loop_contract', tbl = list_type_check spec_type_check loop_desc.loop_contract tbl in  (* : spec list; *)
    let loop_prebody', tbl = stmt_type_check loop_desc.loop_prebody tbl in  (* : t; *)
    let loop_test', tbl = expr_type_check loop_desc.loop_test tbl in  (* : expr; *)
    let loop_postbody', tbl = stmt_type_check loop_desc.loop_postbody tbl in  (* : t; *)
    let tbl = SymbolTbl.pop tbl in

    let (loop_desc': Stmt.loop_desc) = 
    { loop_contract = loop_contract';
      loop_prebody = loop_prebody';
      loop_test = loop_test';
      loop_postbody = loop_postbody';
    }

  in loop_desc', tbl

  and cond_desc_type_check (cond_desc: Stmt.cond_desc) tbl =
    let cond_test', tbl = expr_type_check cond_desc.cond_test tbl in (* : expr; *)
    let tbl = SymbolTbl.push tbl in
    let cond_then', tbl = stmt_type_check cond_desc.cond_then tbl in (* : t; *)
    let tbl = SymbolTbl.pop tbl in
    let tbl = SymbolTbl.push tbl in
    let cond_else', tbl = stmt_type_check cond_desc.cond_else tbl in (* : t; *)
    let tbl = SymbolTbl.pop tbl in

    let (cond_desc': Stmt.cond_desc) = 
    { cond_test = cond_test';
      cond_then = cond_then';
      cond_else = cond_else';
    }

  in cond_desc', tbl

  and ghost_desc_type_check (ghost_desc: Stmt.ghost_desc) tbl =
    let tbl = SymbolTbl.push tbl in
    let ghost_body', tbl = list_type_check stmt_type_check ghost_desc.ghost_body tbl in (* : t list; *)
    let tbl = SymbolTbl.pop tbl in

    let (ghost_desc': Stmt.ghost_desc) = 
    { ghost_body = ghost_body';
    }

    in ghost_desc', tbl

  and stmt_desc_type_check stmt_desc tbl = match stmt_desc with
    | Block stmt_list -> 
        let tbl = SymbolTbl.push tbl in  
        let stmt_list', tbl = list_type_check stmt_type_check stmt_list tbl in
        let tbl = SymbolTbl.pop tbl
      in (Block stmt_list'), tbl
    | Basic basic_stmt_desc -> let basic_stmt_desc', tbl = basic_stmt_desc_type_check basic_stmt_desc tbl
      in (Basic basic_stmt_desc'), tbl
    | Loop loop_desc -> let loop_desc', tbl = loop_desc_type_check loop_desc tbl
      in (Loop loop_desc'), tbl
    | Cond cond_desc -> let cond_desc', tbl = cond_desc_type_check cond_desc tbl
      in (Cond cond_desc'), tbl
    | Ghost ghost_desc -> let ghost_desc', tbl = ghost_desc_type_check ghost_desc tbl
      in (Ghost ghost_desc'), tbl
end

let stmt_type_check = StmtTypeCheck.stmt_type_check

module CallableTypeCheck = struct
  let rec locals_to_string (m: ((ident * Type.var_decl) list)) = match m with
    | [] -> ""
    | l::ls -> Ident.to_string (fst l) ^ " -> " ^ Ident.to_string (snd l).var_name ^ ",   " ^(locals_to_string ls)
    

  let rec call_decl_type_check (call_decl: Callable.call_decl) tbl = 
    let call_decl_kind' = call_decl.call_decl_kind in
    (* Todo: Figure out how to store callable types *)
    let call_decl_name', tbl = call_decl.call_decl_name, tbl in
    let tbl = SymbolTbl.push tbl in
    (* Corresponding SymbolTbl.pop made in proc_def_type_check and func_def_type_check *)
    let call_decl_locals', tbl = ident_map_type_check var_decl_type_check call_decl.call_decl_locals tbl in
    let call_decl_formals', tbl = call_decl.call_decl_formals, tbl in
    let call_decl_returns', tbl = call_decl.call_decl_returns, tbl in
    let call_decl_precond', tbl = list_type_check StmtTypeCheck.spec_type_check call_decl.call_decl_precond tbl in
    let call_decl_postcond', tbl = list_type_check StmtTypeCheck.spec_type_check call_decl.call_decl_postcond tbl in
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
  
  and proc_def_type_check (proc_def: Callable.proc_def) tbl =
    let proc_decl', tbl = call_decl_type_check proc_def.proc_decl tbl in
    let proc_body', tbl = option_type_check stmt_type_check proc_def.proc_body tbl in
    
    let tbl = SymbolTbl.pop tbl in 

    (* Corresponding push made in call_decl_type_check *)
    let (proc_def': Callable.proc_def) =
    { proc_decl = proc_decl'; 
      proc_body = proc_body';
    }

  in proc_def', tbl

  and func_def_type_check (func_def: Callable.func_def) tbl =
    let func_decl', tbl = call_decl_type_check func_def.func_decl tbl in
    let func_body', tbl = option_type_check expr_type_check func_def.func_body tbl in
    let tbl = SymbolTbl.pop tbl in
    (* Corresponding push made in call_decl_type_check *)

    let (func_def': Callable.func_def) =
    { func_decl = func_decl'; 
      func_body = func_body';
    }

  in func_def', tbl

  and callable_type_check (call: Callable.t) tbl : (Callable.t * SymbolTbl.t) = match call with
    | FuncDef func_def -> let func_def', tbl = func_def_type_check func_def tbl 
        in (FuncDef func_def'), tbl
    | ProcDef proc_def -> let proc_def', tbl = proc_def_type_check proc_def tbl
        in (ProcDef proc_def'), tbl

end

let callable_type_check = CallableTypeCheck.callable_type_check

module ModuleTypeCheck = struct
  let rec type_alias_type_check (type_alias: Module.type_alias) tbl = 
    let type_alias_name', tbl = type_alias.type_alias_name, tbl in
    let type_alias_def', tbl = type_alias.type_alias_def, tbl in
    let tbl = (match type_alias_def' with
      | None -> tbl
      | Some tp -> SymbolTbl.add tbl (QualIdent.from_ident type_alias_name') tp ) in
    let type_alias_rep' = type_alias.type_alias_rep in
    let type_alias_loc' = type_alias.type_alias_loc in
  
    let (type_alias': Module.type_alias) =
    { type_alias_name = type_alias_name';
      type_alias_def = type_alias_def';
      type_alias_rep = type_alias_rep';
      type_alias_loc = type_alias_loc';
    }

  in type_alias', tbl

  and mod_alias_type_check (mod_alias: Module.module_alias) tbl = 
    let mod_alias_name', tbl = mod_alias.mod_alias_name, tbl in
    let mod_alias_type', tbl = mod_alias.mod_alias_type, tbl in
    let mod_alias_def', tbl = mod_alias.mod_alias_def, tbl in
    let mod_alias_loc' = mod_alias.mod_alias_loc in
    
    let (mod_alias': Module.module_alias) =
    { mod_alias_name = mod_alias_name';
      mod_alias_type = mod_alias_type';
      mod_alias_def = mod_alias_def';
      mod_alias_loc = mod_alias_loc';
    }

  in mod_alias', tbl


and mod_decl_type_check (mod_decl: Module.module_decl) tbl =
    let mod_decl_name', tbl = mod_decl.mod_decl_name, tbl in
    let mod_decl_formals', tbl = mod_decl.mod_decl_formals, tbl in
    let mod_decl_returns', tbl = mod_decl.mod_decl_returns, tbl in
    let mod_decl_rep', tbl = mod_decl.mod_decl_rep, tbl in
    let mod_decl_mod_defs', tbl = ident_map_type_check mod_decl_type_check mod_decl.mod_decl_mod_defs tbl in
    let mod_decl_mod_aliases', tbl = ident_map_type_check mod_alias_type_check mod_decl.mod_decl_mod_aliases tbl in
    let mod_decl_types', tbl = ident_map_type_check type_alias_type_check mod_decl.mod_decl_types tbl in
    let mod_decl_callables', tbl = ident_map_type_check CallableTypeCheck.call_decl_type_check mod_decl.mod_decl_callables tbl in
    let mod_decl_vars', tbl =  ident_map_type_check var_decl_type_check mod_decl.mod_decl_vars tbl in
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

  in mod_decl', tbl
  
  and import_directive_type_check (imp_dir: Module.import_directive) tbl : (Module.import_directive * SymbolTbl.t) = match imp_dir with
    | ModImport tp_exp -> let tp_exp', tbl = tp_exp, tbl in
        (ModImport tp_exp'), tbl
    | MemImport qual_id -> let qual_id', tbl = qual_id, tbl in
        (MemImport qual_id'), tbl
  
  and member_def_type_check (mem_def: Module.member_def) tbl : (Module.member_def * SymbolTbl.t) = match mem_def with
    | TypeAlias tp_alias -> let tp_alias', tbl = type_alias_type_check tp_alias tbl in
        (TypeAlias tp_alias'), tbl
    | Import imp_dir -> let imp_dir', tbl = import_directive_type_check imp_dir tbl in
        (Import imp_dir'), tbl
    | ModDef mod_def -> let mod_def', tbl = mod_def_type_check mod_def tbl in
        (ModDef mod_def'), tbl
    | ValDef var_defn -> let var_defn', tbl = StmtTypeCheck.var_def_type_check var_defn tbl in
        (ValDef var_defn'), tbl
    | CallDef call -> let call', tbl = callable_type_check call tbl in
        (CallDef call'), tbl

  and mod_def_type_check mod_def tbl = match mod_def with
    | ModImpl mod1 -> let mod', tbl = module_type_check mod1 tbl in
        ((ModImpl mod'), tbl)
    | ModAlias mod_alias -> let mod_alias', tbl = mod_alias_type_check mod_alias tbl in
        ((ModAlias mod_alias'), tbl)
    
  and module_type_check mod1 tbl =
    let tbl = SymbolTbl.push_name mod1.mod_decl.mod_decl_name tbl in

    let mod_def', tbl = list_type_check member_def_type_check mod1.mod_def tbl in
    let mod_decl', tbl = mod_decl_type_check mod1.mod_decl tbl in
    let mod_interface' = mod1.mod_interface in
    
    let tbl = SymbolTbl.pop tbl in

    let (mod': Module.t) = 
    { mod_decl = mod_decl';
      mod_def = mod_def';
      mod_interface = mod_interface';
    }

  in mod', tbl
end

let module_type_check = ModuleTypeCheck.module_type_check


let start_type_check m = module_type_check m (SymbolTbl.push [])
