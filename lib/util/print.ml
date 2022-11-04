(** Pretty printing utility functions *)

open Stdlib.Format

let rec pr_list i pr_sep pr_x ppf = function
  | [] -> ()
  | [x] -> fprintf ppf "%a" (pr_x i) x
  | x :: xs -> fprintf ppf "%a%a%a" (pr_x i) x pr_sep () (pr_list (i + 1) pr_sep pr_x) xs

let pr_list_sep sep pr_x ppf = function
  | [] -> fprintf ppf "_EmptyList_"
  | l -> pr_list 0 (fun ppf _ -> fprintf ppf sep) (fun _ -> pr_x) ppf l
        
let pr_list_comma pr_x ppf =
  pr_list_sep ",@ " pr_x ppf 

let pr_list_nl pr_x ppf = 
  pr_list_sep "@\n" pr_x ppf 

let pr_option pr_x ppf x =
  match x with
  | None -> fprintf ppf "None"
  | Some x' -> pr_x ppf x'

let pr_null ppf _ = fprintf ppf "..."
            
let print_of_format pr x out_ch = fprintf (formatter_of_out_channel out_ch) "%a@?" pr x
       
let string_of_format pr t = pr str_formatter t; flush_str_formatter ()

let print_list out_ch pr xs = print_of_format (pr_list_comma pr) xs out_ch

let _ = pp_set_margin str_formatter 80; Stdlib.Format.set_max_indent 40; 
