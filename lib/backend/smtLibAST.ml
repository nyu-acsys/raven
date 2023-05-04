(** SMT-LIBv2 abstract syntax  *)

open Base
open Util

module SMTIdent = struct
  module T = struct
    type t = { ident_name : string; ident_num : int }
    [@@deriving compare, hash, sexp]

    let to_string id =
      match id.ident_num with
      | 0 -> id.ident_name
      | _ -> Printf.sprintf "%s$%d" id.ident_name id.ident_num
  end

  include T
  (* include Comparable.Make (T) *)

  let pr ppf id = Stdlib.Format.fprintf ppf "%s" (to_string id)
  let pr_list ppf ids = Print.pr_list_comma pr ppf ids

  let pr_ident_map pr_x ppf = 
    let open Stdlib.Format in
    let rec pr_tuple_list ppf (m : (t * 'a) list) =
      match m with
      | [] -> ()
      | (k, v) :: [] -> fprintf ppf "%a -> %a" 
        pr k
        pr_x v
      | (k, v) :: ls ->
          fprintf ppf "%a -> %a@,%a" 
          pr k
          pr_x v
          pr_tuple_list ls
      
    in

    (fun x ->
      let list_of_map = Map.to_alist x in
      if List.is_empty list_of_map then (fprintf ppf "_empty_map_") else
      fprintf ppf "@[<v> %a @]" pr_tuple_list (list_of_map)
  )

  let make ?(num=0) name = { ident_name = name; ident_num = num }
  let name id = id.ident_name

  let fresh =
    let used_names = Hashtbl.create (module String) in
    fun ?(id = 0) (name : string) ->
      let last_index =
        Hashtbl.find used_names name |> Option.value ~default:(-1)
      in
      let new_max = Int.max (last_index + 1) id in
      Hashtbl.set used_names ~key:name ~data:new_max;
      make ~num:new_max name 
end

type smt_ident = SMTIdent.t

type pos = Loc.t

type sort = 
  | IntSort | BoolSort | RealSort
  | AdtSort of smt_ident * adt_def list
  (* why is it smt_ident * adt_def list?  *)
  | FreeSort of smt_ident * sort list
  | ArraySort of sort * sort

and adt_def = smt_ident *  smt_ident list * (smt_ident * (smt_ident * sort) list) list
(* adt_def = name_of_type, optional params list, (constructor, (destructor, sort) list) list *)

type symbol =
  | BoolConst of bool
  | IntConst of int
  | RealConst of float
  | Ident of smt_ident
  | Minus | Plus | Mult | Div | Mod
  | Eq | Gt | Lt | Geq | Leq
  | And | Or | Impl | Not | Ite
  | Select

type binder = Exists | Forall

type term =
  | App of symbol * term list * pos option
  | App_t of term list * pos option 
  | Binder of binder * (smt_ident * sort) list * term * pos option
  | Let of (smt_ident * term) list * term * pos option
  | Annot of term * annotation * pos option
  | Match of term * (term * term) list * pos option

and annotation =
  | Name of smt_ident
  | Pattern of term list
  | As of sort

type command =
  | SetInfo of string * string * pos option
  | SetOption of string * string * pos option
  | SetLogic of string * pos option
  | DeclareSort of smt_ident * int * pos option
  (* | DeclareDatatypes of adt_def list * pos option *)
  | DeclareDatatype of adt_def * pos option
  | DefineSort of smt_ident * smt_ident list * sort * pos option
  | DeclareFun of smt_ident * sort list * sort * pos option
  | DeclareConst of smt_ident * sort * pos option
  | DefineFun of smt_ident * (smt_ident * sort) list * sort * term * pos option
  | Assert of term * pos option
  | Push of int * pos option
  | Pop of int * pos option
  | CheckSat of pos option
  | GetModel of pos option
  | GetUnsatCore of pos option
  | Exit of pos option

type response =
  | Sat
  | Unsat
  | Unknown
  | Model of command list
  | UnsatCore of string list
  | Error of string


  let mk_const ?pos sym = App (sym, [], pos)

  let mk_int ?pos num = mk_const ?pos (IntConst num)
  let mk_real ?pos num = mk_const ?pos (RealConst num)
  let mk_bool ?pos b = mk_const ?pos (BoolConst b)

  let mk_app ?pos sym ts = 
    match sym, ts with
    | Minus, [App (IntConst i, [], _)] -> 
        App (IntConst (-i), [], pos)
    | _, _ -> 
        App (sym, ts, pos)

  let mk_binder ?pos b vs t =
    match vs with
    | [] -> t
    | _ -> Binder (b, vs, t, pos)

  let mk_forall ?pos vs t = mk_binder ?pos Forall vs t

  let mk_exists ?pos vs t = mk_binder ?pos Exists vs t
  
  let mk_let ?pos defs t = Let (defs, t, pos)
  
  let mk_annot ?pos t a = Annot (t, a, pos)

  let mk_match ?pos t t_t_list = Match (t, t_t_list, pos)

  let mk_and ?pos ts = 
    match ts with
    | [] -> (mk_bool true)
    | [term] -> term
    | ts -> mk_app ?pos And ts

  let mk_or ?pos ts = 
    match ts with
    | [] -> (mk_bool false)
    | [term] -> term
    | ts -> mk_app ?pos Or ts

  let mk_not ?pos t = mk_app ?pos Not [t]

  let mk_impl ?pos t1 t2 = mk_app ?pos Impl [t1; t2]

  let mk_eq ?pos t1 t2 = mk_app ?pos Eq [t1; t2]

  let mk_select ?pos t1 t2 = mk_app ?pos Select [t1; t2]

  let mk_leq ?pos t1 t2 = mk_app ?pos Leq [t1; t2]
  let mk_lt ?pos t1 t2 = mk_app ?pos Lt [t1; t2]

  let mk_geq ?pos t1 t2 = mk_app ?pos Geq [t1; t2]
  let mk_gt ?pos t1 t2 = mk_app ?pos Gt [t1; t2] 

  let mk_ite ?pos t0 t1 t2 = mk_app ?pos Ite [t0; t1; t2]

  let term_of_string ?pos str = mk_app ?pos (Ident (SMTIdent.make str)) []

  
  let mk_set_logic ?pos l = SetLogic (l, pos)
      
  let mk_set_option ?pos o v = SetOption (o, v, pos)
  
  let mk_set_info ?pos i v = SetInfo (i, v, pos)
  
  let mk_declare_sort ?pos id arity = DeclareSort (id, arity, pos)
      
  let mk_declare_datatype ?pos adt = DeclareDatatype (adt, pos)
  
  let mk_declare_fun ?pos id arg_srts res_srt = DeclareFun (id, arg_srts, res_srt, pos)

  let mk_declare_const ?pos id srt = DeclareConst (id, srt, pos)
  
  let mk_define_sort ?pos id args srt = DefineSort (id, args, srt, pos)
  
  let mk_define_fun ?pos id args res_srt t = DefineFun (id, args, res_srt, t, pos)
  
  let mk_assert ?pos t = Assert (t, pos)
  
  let mk_push ?pos n = Push (n, pos)
  
  let mk_pop ?pos n = Pop (n, pos)
  
  let mk_check_sat ?pos () = CheckSat pos
  
  let mk_get_model ?pos () = GetModel pos
  
  let mk_get_unsat_core ?pos () = GetModel pos
  
  let mk_exit ?pos () = Exit pos


  (* --- *)

  let smt_ident_of_term term = 
    match term with
    | App (Ident ident, [], _) -> ident
    | _ -> raise (Failure "smt_ident_of_term failed: found unexpected term")

  let unfold_assert cmd = match cmd with
  | Assert (term, _) -> term
  | _ -> Error.error_simple "Unfold_assert called on command which is not assert"

(** Pretty printing *)

open Stdlib.Format

let string_of_symbol = function
  | BoolConst b -> Printf.sprintf "%b" b
  | IntConst i -> Int.to_string i
  | RealConst r -> Float.to_string r
  | Ident id -> SMTIdent.to_string id
  | Plus -> "+"
  | Minus -> "-"
  | Mult -> "*"
  | Div -> "/"
  | Mod -> "mod"
  | Eq -> "="
  | Leq -> "<="
  | Geq -> ">="
  | Lt -> "<"
  | Gt -> ">"
  | And -> "and"
  | Or -> "or"
  | Impl -> "=>"
  | Not -> "not"
  | Ite -> "ite"
  | Select -> "select"

let pr_ident ppf id = fprintf ppf "%s" (SMTIdent.to_string id)

let rec pr_idents ppf = function
  | [] -> ()
  | [id] -> pr_ident ppf id
  | id :: ids -> fprintf ppf "%a@ %a" pr_ident id pr_idents ids

let rec pr_sort ppf = function
  | AdtSort  (id, _) -> pr_ident ppf id
  | FreeSort (id, []) -> pr_ident ppf id
  | FreeSort (id, srts) -> fprintf ppf "@[<2>(%s@ %a)@]" (SMTIdent.to_string id) pr_sorts srts
  | BoolSort -> fprintf ppf "Bool"
  | IntSort -> fprintf ppf "Int"
  | RealSort -> fprintf ppf "Real"
  | ArraySort (s1, s2) -> fprintf ppf "@[<2>(Array %a %a)@]" pr_sort s1 pr_sort s2 

and pr_sorts ppf = function
  | [] -> ()
  | [srt] -> pr_sort ppf srt
  | srt :: srts -> fprintf ppf "%a@ %a" pr_sort srt pr_sorts srts

let pr_sym ppf sym = fprintf ppf "%s" (string_of_symbol sym)

let pr_binder ppf b =
  let b_str = match b with
  | Forall -> "forall"
  | Exists -> "exists"
  in 
  fprintf ppf "%s" b_str

let pr_var_decl ppf (x, srt) =
  fprintf ppf "@[<1>(%a@ %a)@]" pr_ident x pr_sort srt

let rec pr_var_decls ppf = function
  | [] -> ()
  | [v] -> fprintf ppf "%a" pr_var_decl v
  | v :: vs -> fprintf ppf "%a@ %a" pr_var_decl v pr_var_decls vs

let rec pr_term ppf = function
  | App (sym, [], _) -> pr_sym ppf sym
  | App (sym, ts, _) -> fprintf ppf "@[<2>(%a@ %a)@]" pr_sym sym pr_terms ts
  | App_t (ts, _) -> fprintf ppf "@[<2>(%a)@]" pr_terms ts 
  | Binder (b, vs, f, _) -> 
      fprintf ppf "@[<8>(%a@ @[<1>(%a)@]@ %a)@]" pr_binder b pr_var_decls vs pr_term f
  | Let (decls, t, _) ->
      fprintf ppf "@[<5>(let@ (%a) %a)@]" pr_let_decls decls pr_term t
  | Annot (t, a, _) -> pr_annot ppf (t, a)
  | Match (t, t_t_list, _) -> fprintf ppf "@[ (match@ %a (%a))@]" pr_term t pr_list_pair_of_terms t_t_list

and pr_terms ppf = function
  | [] -> ()
  | [t] -> pr_term ppf t
  | t :: ts -> fprintf ppf "%a@ %a" pr_term t pr_terms ts

and pr_list_pair_of_terms ppf = function
  | [] -> ()
  | (t1, t2) :: ts -> fprintf ppf "(%a@ %a) %a" pr_term t1 pr_term t2 pr_list_pair_of_terms ts

and pr_let_decl ppf (id, t) =
  fprintf ppf "@[<2>(%a@ %a)@]" pr_ident id pr_term t

and pr_let_decls ppf = function
  | [] -> ()
  | [decl] -> pr_let_decl ppf decl
  | decl :: decls ->
      fprintf ppf "%a@ %a" pr_let_decl decl pr_let_decls decls
        
and pr_annot ppf (t, a) =
  match a with
  | Name id ->
      let id2 = Str.global_replace (Str.regexp " \\|(\\|)\\|<\\|>") "-" (SMTIdent.to_string id) in
      fprintf ppf "@[<3>(! %a@ @[:named@ %s@])@]" pr_term t id2
  | Pattern [] -> ()
  | Pattern ts ->
      fprintf ppf "@[<3>(! %a@ @[:pattern@ (%a)@])@]" pr_term t pr_terms ts
  | As srt ->
      fprintf ppf "@[<4>(as@ %a@ %a)@]" pr_term t pr_sort srt

let print_term out_ch t = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_term t

let rec pr_adt_args ppf = function
  | [] -> ()
  | (id, srt) :: args ->
      fprintf ppf "@ (%a@ %a)%a" pr_ident id pr_sort srt pr_adt_args args
    
let rec pr_adt_constrs ppf = function
  | [] -> ()
  | (id, args) :: cnstrs ->
      fprintf ppf "@ (%a%a)%a" pr_ident id pr_adt_args args pr_adt_constrs cnstrs

(* let rec pr_adts ppf = function
  | [] -> ()
  | (id, cnstrs) :: adts ->
      fprintf ppf "@ (%a%a)%a" pr_ident id pr_adt_constrs cnstrs pr_adts adts *)

let rec pr_adt ppf (id, params, constrs) =
match params with
| [] -> fprintf ppf "@[%a (%a)@]" pr_ident id pr_adt_constrs constrs
| _ -> fprintf ppf "@[%a (par (%a) (%a))@]" pr_ident id pr_idents params pr_adt_constrs constrs


        
let pr_command ppf = function
  | SetInfo (i, v, _) ->
      fprintf ppf "@[<10>(set-info@ %s@ %s)@]@\n" i v
  | SetOption (o, v, _) ->
      fprintf ppf "@[<12>(set-option@ %s@ %s)@]@\n" o v
  | SetLogic (l, _) ->
      fprintf ppf "@[<11>(set-logic@ %s)@]@\n" l
  | DeclareSort (id, n, _) ->
      fprintf ppf "@[<14>(declare-sort@ %a@ %d)@]@\n" pr_ident id n
  | DeclareDatatype (adt, _) ->
      fprintf ppf "@[<19>(declare-datatype@ @[<2>%a@])@]@\n" pr_adt adt
  | DefineSort (id, svs, srt, _) ->
      fprintf ppf "@[<13>(define-sort@ %a@ (%a)@ %a)@]@\n" pr_ident id pr_idents svs pr_sort srt
  | DeclareFun (id, srts, srt, _) ->
      fprintf ppf "@[<13>(declare-fun@ %a@ (%a)@ %a)@]@\n" pr_ident id pr_sorts srts pr_sort srt
  | DeclareConst (id, srt, _) ->
    fprintf ppf "@[<13>(declare-const@ %a@ %a)@]\n" pr_ident id pr_sort srt
  | DefineFun (id, vs, srt, t, _) ->
      fprintf ppf "@[<12>(define-fun@ %a@ (%a)@ %a@ %a)@]@\n" pr_ident id pr_var_decls vs pr_sort srt pr_term t
  | Assert (t, _) ->
      fprintf ppf "@[<8>(assert@ %a)@]@\n" pr_term t
  | Push (n, _) -> fprintf ppf "@[<6>(push@ %d)@]@\n" n
  | Pop (n, _) -> fprintf ppf "@[<5>(pop@ %d)@]@\n" n
  | CheckSat _ -> fprintf ppf "(check-sat)@\n"
  | GetModel _ -> fprintf ppf "(get-model)@\n"
  | GetUnsatCore _ -> fprintf ppf "(get-unsat-core)@\n"
  | Exit _ -> fprintf ppf "(exit)@\n"

let print_comment out_ch cmnt = fprintf (formatter_of_out_channel out_ch) "; %s\n@?" cmnt

let rec pr_commands ppf = function
  | [] -> ()
  | cmd :: cmds ->
      fprintf ppf "%a%a" pr_command cmd pr_commands cmds

let print_command out_ch cmds = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_command cmds
let print_commands out_ch cmds = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_commands cmds
