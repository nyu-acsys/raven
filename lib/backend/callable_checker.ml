open Base
open Ast
open Util
open Error
open Frontend__Process_ast

let rec alpha_renaming (expr: expr) (map: expr qual_ident_map) : expr =
  match expr with
  | App (constr, expr_list, expr_attr) ->
    let expr_list = List.map expr_list ~f:(fun expr -> alpha_renaming expr map) in

    (match constr with
    | Var qual_ident ->
      (match Map.find map qual_ident with
      | None ->
        App (Var qual_ident, expr_list, expr_attr)
      | Some expr' ->
        expr'
      )
    | _ -> App (constr, expr_list, expr_attr)

    )

  | Binder (binder, var_decl_list, expr, expr_attr) ->
    (* TODO: Rename the var_decl to avoid clashing with variables in the map *)
    let expr = alpha_renaming expr map in
    Binder (binder, var_decl_list, expr, expr_attr)

module CallableChecker = struct
  type atomicity_status = | Default | Opened | Stepped
  type atomicity_constraints = {
    status : atomicity_status;
    opened_invariants : expr list;
    opened_atomic_token : ident option;
    ghost_block : bool;
  }

  let default_atomicity_constraint : atomicity_constraints = {
    status = Default;
    opened_invariants = [];
    opened_atomic_token = None;
    ghost_block = false;
  }

  let atom_step (atom_constr: atomicity_constraints) =
    match atom_constr.status with
    | Default -> atom_constr
    | Opened -> 
      (match atom_constr.ghost_block with
      | true -> atom_constr
      | false -> { atom_constr with
        status = Stepped;
        }
      )
    | Stepped -> 
      (match atom_constr.ghost_block with
      | true -> atom_constr
      | false -> raise (Error.Generic_Error "Violated Atomicity Constraints")
      )
      

  let rec stmt_preprocessor (stmt: Stmt.t) (tbl: SymbolTbl.t) ~(atom_constr: atomicity_constraints) : atomicity_constraints * Stmt.t  = 
    (* This function replaces any Call() stmts with appropriate inhale and exhale statements by looking at its spec from tbl *)
    let open Stmt in
    let atom_const, stmt_desc = 
    (match stmt.stmt_desc with 
    | Block stmt_list ->
      let atom_const, stmt_list = List.fold_map stmt_list ~init:atom_constr ~f:(fun atom_const stmt -> stmt_preprocessor stmt tbl ~atom_constr:atom_const) in

      atom_const, Block stmt_list
    
    | Loop _loop_desc ->
      let str = Print.string_of_format Stmt.pr stmt in
      raise (Generic_Error (str ^ ": InternalError: Loops not presently supported."))
    
    | Cond cond_desc ->
      let cond_test = cond_desc.cond_test in
      let atom_constr, cond_then = stmt_preprocessor cond_desc.cond_then tbl ~atom_constr:atom_constr in
      let atom_constr, cond_else = stmt_preprocessor cond_desc.cond_else tbl ~atom_constr:atom_constr in

      let cond_desc = {
        cond_test;
        cond_then;
        cond_else;
      }

      in
      atom_constr, Cond cond_desc
    
    | Ghost ghost_desc ->
      let atom_constr', ghost_body = stmt_preprocessor ghost_desc.ghost_body tbl ~atom_constr:{atom_constr with ghost_block = true;} in

      let ghost_desc = { 
        ghost_body;
      }
      (* TODO: Implement Atomic Constraints for Ghost blocks correctly *)
      in
      {atom_constr' with ghost_block = false;}, Ghost ghost_desc


    | Basic basic_stmt_desc ->
      (match basic_stmt_desc with
      | VarDef _
      | Assume _
      | Assert _
      | New _
      | Assign _
      | Havoc _ ->
        (try
          (atom_step atom_constr), Basic basic_stmt_desc
        with
          Generic_Error str -> Error.error stmt.stmt_loc str)

      | Call call_desc -> 
        (match SymbolTbl.find tbl call_desc.call_name with
        | Some Callable call_decl ->
          let formal_args_truncated, _ = List.split_n call_decl.call_decl_formals (List.length call_desc.call_args) in
          let map = List.fold (List.zip_exn formal_args_truncated call_desc.call_args) ~init:(Map.empty (module QualIdent)) ~f:(fun map (formal_arg, call_arg) -> Map.add_exn map ~key:(QualIdent.from_ident formal_arg) ~data:call_arg) in

          let exhale_list : Stmt.t list = List.map call_decl.call_decl_precond 
            ~f:(fun spec -> {stmt_desc = Basic (Exhale (alpha_renaming spec.spec_form map)); stmt_loc = stmt.stmt_loc}) in
          
          let inhale_list : Stmt.t list = List.map call_decl.call_decl_postcond 
          ~f:(fun spec -> {stmt_desc = Basic (Inhale (alpha_renaming spec.spec_form map)); stmt_loc = stmt.stmt_loc}) in

          (match atom_constr.status with
          | Default ->
            atom_constr, Block (exhale_list @ inhale_list)
            
          | Opened ->
            { atom_constr with status = Stepped}, Block (exhale_list @ inhale_list)

          | Stepped -> 
            Error.error stmt.stmt_loc "Violated atomicity constraints"
          )
        | Some tp_elem -> Error.error stmt.stmt_loc ("Expected Callable in TpEnv; found " ^ SymbolTbl.typing_env_to_string tp_elem)
        | None -> Error.error stmt.stmt_loc ("Expected Callable in TpEnv; " ^ QualIdent.to_string call_desc.call_name ^ " not found. ")
        )
        

      | Return _expr_list -> 
        (match atom_constr.status with
        | Default ->
          atom_constr, Basic basic_stmt_desc
        | _ -> 
          Error.error stmt.stmt_loc ("Did not close all atomic stmts")
        )


      | Fold _
      | Unfold _ -> 
        atom_constr, Basic basic_stmt_desc

      | BindAU _ident -> 
        atom_constr, Basic basic_stmt_desc

      | OpenAU open_au -> 
        (match atom_constr.status with
        | Default -> 
          { atom_constr with status = Opened; opened_atomic_token = Some open_au}, Basic basic_stmt_desc
        | Opened ->
          (match atom_constr.opened_atomic_token with
          | None -> { atom_constr with opened_atomic_token = Some open_au}, Basic basic_stmt_desc
          | Some iden -> Error.error stmt.stmt_loc ("Cannot opened another atomic triple when " ^ Ident.to_string iden ^ " is opened")
          )
        | Stepped -> Error.error stmt.stmt_loc ("Cannot open another atomic triple; first close previous atomic stmts.")
        )

      | AbortAU ident 
      | CommitAU ident -> 
        (match atom_constr.status with
        | Default -> Error.error stmt.stmt_loc "Error: Cannot abortAU since nothing is open"
        | Opened
        | Stepped ->
          (match atom_constr.opened_atomic_token with
          | None -> Error.error stmt.stmt_loc "Error: Cannot abortAU since no Atomic Token is open"
          | Some ident' -> 
            if Ident.compare ident ident' = 0 then 
              (match atom_constr.opened_invariants with
              | [] -> default_atomicity_constraint, Basic basic_stmt_desc
              | _inv_list -> { atom_constr with opened_atomic_token = None}, Basic basic_stmt_desc
              )
            else
              Error.error stmt.stmt_loc ("Cannot AbortAU as " ^ Ident.to_string ident' ^ " AU is open")
          )
        
        )

      | OpenInv expr -> 
        (match atom_constr.status with
        | Default
        | Opened ->
          { atom_constr with status = Opened; opened_invariants = expr :: atom_constr.opened_invariants}, Basic basic_stmt_desc
        | Stepped ->
          { atom_constr with opened_invariants = expr :: atom_constr.opened_invariants}, Basic basic_stmt_desc
        )

      | CloseInv expr ->
        (match atom_constr.status with
        | Default -> Error.error stmt.stmt_loc "Cannot CloseInv, nothing opened."
        | Opened 
        | Stepped ->
          (match atom_constr.opened_invariants with
          | [] -> Error.error stmt.stmt_loc "Cannot CloseInv. Invariant not found."
          | [expr'] -> 
            if Expr.compare expr expr' = 0 then
              (match atom_constr.opened_atomic_token with
              | None -> default_atomicity_constraint, Basic basic_stmt_desc
              | Some _ -> {atom_constr with opened_invariants = []}, Basic basic_stmt_desc
              )
            else
              Error.error stmt.stmt_loc "Cannot CloseInv; invariants need to be closed in reverse order of opening"

          | expr' :: expr_list ->
            if Expr.compare expr expr' = 0 then
              {atom_constr with opened_invariants = expr_list}, Basic basic_stmt_desc
            else
              Error.error stmt.stmt_loc "Cannot CloseInv; invariants need to be closed in reverse order of opening"
          )
        )


      | Inhale _ 
      | Exhale _ -> 
        Error.error stmt.stmt_loc "Inhale/Exhale stmt not expected in AST at this stage."
      )


    ) in
      
    atom_const, {stmt_desc = stmt_desc; stmt_loc = stmt.stmt_loc}

  let stmt_preprocessor_simple (stmt: Stmt.t) (tbl: SymbolTbl.t) : atomicity_constraints * Stmt.t = stmt_preprocessor stmt tbl ~atom_constr:default_atomicity_constraint
  
end