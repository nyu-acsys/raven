(* open Base
open Ast
open Util
open Error
open Frontend

open Z3


module Z3Util = struct

type type_terms = {
  type_sort : Z3.Sort.sort;
  type_heap_chunk_sort : Z3.Sort.sort;
  type_heap_sort : Z3.Sort.sort;
  type_heap_chunk_add_func : Z3.FuncDecl.func_decl;
  type_heap_chunk_remove_func : Z3.FuncDecl.func_decl;
  type_heap_chunk_validity_func : Z3.FuncDecl.func_decl;
}

and 

field_terms = {
  field_sort : Z3.Sort.sort;
  field_validity_func : Z3.FuncDecl.func_decl;
}






(* let initialize_type_field ctx solver (type: Ast.QualIdent.t) = 
  let  *)

let add_preamble ctx solver =
  let loc_sort = Z3.Sort.mk_uninterpreted_s ctx "loc" in
  let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in


  let initialize_type ctx solver (type_: Ast.Type.t) (tbl: Process_ast.SymbolTbl.t) : (Z3.Solver.solver * type_terms) = 
    (match type_ with
    | App (constr, type_list, type_attr) ->
      (match constr with
      | Int ->
        (
          let int_sort = int_sort in
          let int_heap_null_constructor = (Z3.Datatype.mk_constructor ctx  (Z3.Symbol.mk_string ctx "int_heapchunk_null") (Z3.Symbol.mk_string ctx "is_int_heapchunk_null") [] [] []) in
          let int_heap_fracchunk_constructor = (Z3.Datatype.mk_constructor ctx  (Z3.Symbol.mk_string ctx "int_heapchunk_frac") (Z3.Symbol.mk_string ctx "is_int_heapchunk_frac") [(Z3.Symbol.mk_string ctx "Val"); (Z3.Symbol.mk_string ctx "Own")] [Some (Z3.Arithmetic.Integer.mk_sort ctx); Some (Z3.Arithmetic.Real.mk_sort ctx)] []) in
          let int_heap_top_constructor = (Z3.Datatype.mk_constructor ctx  (Z3.Symbol.mk_string ctx "int_heapchunk_top") (Z3.Symbol.mk_string ctx "is_int_heapchunk_top") [] [] []) in
        let int_heap_chunk_sort = Z3.Datatype.mk_sort ctx (Z3.Symbol.mk_string ctx "int_heapchunk") [int_heap_null_constructor; int_heap_fracchunk_constructor; int_heap_top_constructor] in
  
  
        let int_heap_sort = Z3.Z3Array.mk_sort ctx loc_sort int_heap_chunk_sort in
        let int_heap_chunk_add_func = Z3.FuncDecl.mk_func_decl_s ctx "int_heapchunk_add" [int_heap_chunk_sort; int_heap_chunk_sort] int_heap_chunk_sort in
        let int_heap_chunk_remove_func = Z3.FuncDecl.mk_func_decl_s ctx "int_heapchunk_remove" [int_heap_chunk_sort; int_heap_chunk_sort] int_heap_chunk_sort in
        let int_heap_chunk_validity_func = Z3.FuncDecl.mk_func_decl_s ctx "int_heapchunk_valid" [int_heap_chunk_sort] (Z3.Boolean.mk_sort ctx) in

        let _ = Z3.Solver.add solver [Z3.Quantifier.expr_of_quantifier (Z3.Quantifier.mk_forall_const ctx)]
        
  
        let type_terms = {
          type_sort = int_sort;
          type_heap_chunk_sort = int_heap_chunk_sort;
          type_heap_sort = int_heap_sort;
          type_heap_chunk_add_func = int_heap_chunk_add_func;
          type_heap_chunk_remove_func = int_heap_chunk_remove_func;
          type_heap_chunk_validity_func = int_heap_chunk_validity_func;
        } in
        (solver, type_terms))
      | Bool
      | Ref
      | Map
      | Set
      | Data var_decl_list
      ) 
    )


let initialize_z3 () =
  let cfg = [("model", "true")] in
  let ctx = mk_context cfg in
  let solver = Z3.Solver.mk_solver ctx None in

end *)