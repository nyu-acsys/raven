open Base
open Ast
open Util
open Error
open Frontend__Process_ast

let rec check_module (m: Module.t) (tbl: SymbolTbl.t) =
  let _ = List.map m.members.mod_defs ~f:(fun m -> check_module m tbl) in

  
  List.map m.members.call_defs 
  ~f:(fun call_def -> 
    match call_def with
    | FuncDef _func_def -> ()
    | ProcDef proc_def -> 
      (match proc_def.proc_body with
      | None -> ()
      | Some stmt ->
        let _atom_constr, stmt' = Callable_checker.CallableChecker.stmt_preprocessor_simple stmt tbl in

        Print.print_of_format Stmt.pr stmt' Stdio.stdout;
        Stdio.print_endline "";
        Stdio.print_endline "";
      )
    )