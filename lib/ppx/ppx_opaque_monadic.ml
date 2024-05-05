open Ppxlib


let expand e =
  let return n = Some (Ast_builder.Default.eint ~loc:e.pexp_loc n) in
  
  match e.pexp_desc with
  | Pexp_apply (_, arg_list) -> return (List.length arg_list)
  | _ -> return 0

let rule = Context_free.Rule.special_function "n_args" expand

let _ = Driver.register_transformation ~rules:[ rule ] "special_function_demo"