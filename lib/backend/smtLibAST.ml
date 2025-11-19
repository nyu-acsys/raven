(** SMT-LIBv2 abstract syntax  *)

open Base
open Util
open Ast

(* type pos = Loc.t *)

type term = Ast.expr
type sort = Ast.Type.t

type smt_ident = qual_ident

and adt_def =
  smt_ident * smt_ident list * (smt_ident * (smt_ident * sort) list) list
(* name     optional params  (constructor, (destructor, sort) list) list *)

module PreambleConsts = struct
  let loc_ident = QualIdent.from_ident (Ident.make Util.Loc.dummy "$Loc" 0)

  let atomic_token_ident =
    QualIdent.from_ident (Ident.make Util.Loc.dummy "$AtomicToken" 0)
  (* let loc_sort = FreeSort (loc_ident, []) *)
end

type command =
  | SetInfo of string * string * location option
  | SetOption of string * string * location option
  | SetLogic of string * location option
  | DeclareSort of smt_ident * int * location option
  | DeclareDatatype of adt_def * location option
  | DeclareDatatypes of adt_def list * location option
  | DefineSort of smt_ident * smt_ident list * sort * location option
  | DeclareFun of smt_ident * sort list * sort * location option
  | DeclareConst of smt_ident * sort * location option
  | DefineFun of
      smt_ident * (smt_ident * sort) list * sort * term * location option
  | DefineFunRec of
      smt_ident * (smt_ident * sort) list * sort * term * location option
  (* | DefineFunsRec of (smt_ident * (smt_ident * sort) list * sort * term) list * location option *)
  | Assert of term * location option
  | Push of int * location option
  | Pop of int * location option
  | CheckSat of location option
  | GetModel of location option
  | GetUnsatCore of location option
  | Exit of location option

type response =
  | Sat
  | Unsat
  | Unknown
  | Model of command list
  | UnsatCore of string list
  | Error of string

let mk_set_logic ?loc l = SetLogic (l, loc)
let mk_set_option ?loc o v = SetOption (o, v, loc)
let mk_set_info ?loc i v = SetInfo (i, v, loc)
let mk_declare_sort ?loc id arity = DeclareSort (id, arity, loc)
let mk_declare_datatype ?loc adt = DeclareDatatype (adt, loc)
let mk_declare_datatypes ?loc adts = DeclareDatatypes (adts, loc)

let mk_declare_fun ?loc id arg_srts res_srt =
  DeclareFun (id, arg_srts, res_srt, loc)

let mk_declare_const ?loc id srt = DeclareConst (id, srt, loc)
let mk_define_sort ?loc id args srt = DefineSort (id, args, srt, loc)
let mk_define_fun ?loc id args res_srt t = DefineFun (id, args, res_srt, t, loc)
let mk_assert ?loc t = Assert (t, loc)
let mk_push ?loc n = Push (n, loc)
let mk_pop ?loc n = Pop (n, loc)
let mk_check_sat ?loc () = CheckSat loc
let mk_get_model ?loc () = GetModel loc
let mk_get_unsat_core ?loc () = GetModel loc
let mk_exit ?loc () = Exit loc

(** Pretty printing *)

open Stdlib.Format

let pr_smt_ident ppf id = 
  let smt_ident_sanitize_map = (
    function 
    | '\'' -> '_'
    | x -> x
  ) in

  let sanitized_ident = 
    if QualIdent.(id = QualIdent.from_ident (Ident.make Loc.dummy "_" 0)) then 
      QualIdent.from_ident (Ident.make Loc.dummy "_0" 0) 
    else QualIdent.sanitize smt_ident_sanitize_map id in

  (* Logs.debug (fun m -> m 
    "smtLibAST.pr_smt_ident: 
      Original Ident: %a
      Sanitized ident: %a"
      QualIdent.pr id
      QualIdent.pr sanitized_ident
  ); *)


  QualIdent.pr ppf sanitized_ident

let rec pr_smt_idents ppf = function
  | [] -> ()
  | [ id ] -> pr_smt_ident ppf id
  | id :: ids -> fprintf ppf "%a@ %a" pr_smt_ident id pr_smt_idents ids

let rec pr_sort ppf (sort : sort) =
  match sort with
  | App (Int, [], _) -> fprintf ppf "Int"
  | App (Real, [], _) -> fprintf ppf "Real"
  | App (Bool, [], _) -> fprintf ppf "Bool"
  | App (Ref, [], _) -> pr_smt_ident ppf PreambleConsts.loc_ident
  | App (Var qual_iden, [], _) -> pr_smt_ident ppf qual_iden
  | App (Map, [ srt; App (Bool, _, _)], _) -> fprintf ppf "@[<2>(Set %a)@]" pr_sort srt
  | App (Map, [ srt1; srt2 ], _) ->
      fprintf ppf "@[<2>(Array %a %a)@]" pr_sort srt1 pr_sort srt2
  | App (Data (id, _), [], _) -> pr_smt_ident ppf id
  | App (Prod, srts, _) ->
      fprintf ppf "@[<2>($tuple_%i %a)@]" (List.length srts) pr_sorts srts
  | App (AtomicToken qid, [], _) -> pr_smt_ident ppf (PreambleConsts.atomic_token_ident)
  | App (Num, _, _)
  | App (Perm, _, _)
  | App (Bot, _, _)
  | App (Any, _, _)
  | App (Fld, _, _) ->
      Error.internal_error (Type.to_loc sort)
        ("pr_sort: unexpected sort: " ^ Type.to_string sort)
  | _ ->
      Logs.debug (fun m ->
          m "pr_sort: unexpected sort %s" (Type.to_string sort));
      assert false

and pr_sorts ppf = function
  | [] -> ()
  | [ srt ] -> pr_sort ppf srt
  | srt :: srts -> fprintf ppf "%a@ %a" pr_sort srt pr_sorts srts

let pr_var_decl ppf (x, srt) =
  fprintf ppf "@[<1>(%a@ %a)@]" pr_smt_ident x pr_sort srt

let rec pr_var_decls ppf = function
  | [] -> ()
  | [ v ] -> fprintf ppf "%a" pr_var_decl v
  | v :: vs -> fprintf ppf "%a@ %a" pr_var_decl v pr_var_decls vs

let term_constr_to_string loc (constr : Expr.constr) : string =
  match constr with
  | Bool _ | Int _ | Real _ | Gt | Lt | Geq | Leq | Plus | Minus | Mult | Div
  | DataConstr _ | DataDestr _ ->
      Expr.constr_to_string constr
  | Mod -> "mod"
  | Not -> "not"
  | MapLookUp -> "select"
  | MapUpdate -> "store"
  | Eq -> "="
  | Union -> "union"
  | Inter -> "intersection"
  | Elem -> "select"
  | Subseteq -> "subset"
  | And -> "and"
  | Or -> "or"
  | Impl -> "=>"
  | Var id -> Stdlib.Format.asprintf "%a" pr_smt_ident id
  | Ite -> "ite"
  | _ ->
      Error.internal_error loc
        ("term_constr_to_string: unexpected constr"
        ^ Expr.constr_to_string constr)

let rec pr_term ppf (term : term) =
  match term with
  | App (constr, expr_list, _) -> (
      match (constr, expr_list) with
      | ( (( Bool _ | Int _ | Real _ | Not | MapLookUp | MapUpdate | Eq | Gt
           | Lt | Geq | Leq | Union | Inter | Subseteq | And | Or | Plus | Minus
           | Mult | Div | Mod | DataConstr _ | DataDestr _ | Ite | Var _ ) as
           sym),
          ts ) -> (
          match expr_list with
          | [] ->
              fprintf ppf "@[%s@]"
                (term_constr_to_string (Expr.to_loc term) sym)
          | _ ->
              fprintf ppf "@[<2>(%s@ %a)@]"
                (term_constr_to_string (Expr.to_loc term) sym)
                pr_terms ts)
      | Impl, [ t1; t2 ] ->
          if Expr.alpha_equal t1 (Expr.mk_bool true) then
            fprintf ppf "%a" pr_term t2
          else fprintf ppf "@[<2>(=>@ %a@ %a)@]" pr_term t1 pr_term t2
      | Elem, [ t; s ] ->
          fprintf ppf "@[<2>(select@ %a@ %a)@]" pr_term s pr_term t
      | Null, [] -> fprintf ppf "null"
      | Empty, [] ->
          fprintf ppf "((as const %a) false)" pr_sort (Expr.to_type term)
      | Uminus, [ t ] -> fprintf ppf "@[<2>(* -1 @ %a)@]" pr_term t
      | Setenum, es ->
          let empty_set =
            asprintf "((as const %a) false)" pr_sort (Expr.to_type term)
          in
          let str =
            List.fold es ~init:empty_set ~f:(fun acc e ->
                asprintf "(store %s %a true)" acc pr_term e)
          in
          fprintf ppf "%s" str
      | TupleLookUp, [ tuple_expr; index ] ->
          let arity =
            match Expr.to_type tuple_expr with
            | App (Prod, ts, _) -> List.length ts
            | _ ->
                Error.internal_error (Expr.to_loc term)
                  ("pr_term: unexpected term" ^ Expr.to_string term)
          in
          let index_num = Expr.to_int index 
          in
          fprintf ppf "@[<2>($tuple_%i_%i@ %a)@]" arity index_num pr_term
            tuple_expr
      | Tuple, es -> (
          match List.length es with
          | 0 -> fprintf ppf "@[<2>$tuple_0 @]"
          | _ ->
              fprintf ppf "@[<2>($tuple_%i %a)@]" (List.length es) pr_terms es)
      | Diff, _ | Read, _ | Own, _ | _ ->
          Error.internal_error (Expr.to_loc term)
            ("pr_term: unexpected term" ^ Expr.to_string term))
  | Binder (b, vs, trgs, f, _) -> (
      let vs =
        List.map vs ~f:(fun v -> (QualIdent.from_ident v.var_name, v.var_type))
      in
      match trgs with
      | [] ->
          fprintf ppf "@[(%s @[(%a)@,%a)@]@]" (Expr.binder_to_string b)
            pr_var_decls vs pr_term f
      | _ ->
          fprintf ppf "@[(%s @[(%a)@,(! %a %a)@])@]" (Expr.binder_to_string b)
            pr_var_decls vs pr_term f pr_trgs trgs)

and pr_terms ppf = function
  | [] -> ()
  | [ t ] -> pr_term ppf t
  | t :: ts -> fprintf ppf "%a@ %a" pr_term t pr_terms ts

and pr_list_pair_of_terms ppf = function
  | [] -> ()
  | (t1, t2) :: ts ->
      fprintf ppf "(%a@ %a) %a" pr_term t1 pr_term t2 pr_list_pair_of_terms ts

and pr_let_decl ppf (id, t) =
  fprintf ppf "@[<2>(%a@ %a)@]" pr_smt_ident id pr_term t

and pr_let_decls ppf = function
  | [] -> ()
  | [ decl ] -> pr_let_decl ppf decl
  | decl :: decls -> fprintf ppf "%a@ %a" pr_let_decl decl pr_let_decls decls

and pr_trgs ppf = function
  | [] -> ()
  | [ t ] -> fprintf ppf ":pattern (%a)" pr_terms t
  | t :: ts -> fprintf ppf ":pattern (%a) @,%a" pr_terms t pr_trgs ts

(* and pr_annot ppf (t, a) =
   match a with
   | Name id ->
       let id2 = Str.global_replace (Str.regexp " \\|(\\|)\\|<\\|>") "-" (SMTIdent.to_string id) in
       fprintf ppf "@[<3>(! %a@ @[:named@ %s@])@]" pr_term t id2
   | Pattern [] -> ()
   | Pattern ts ->
       fprintf ppf "@[<3>(! %a@ @[:pattern@ (%a)@])@]" pr_term t pr_terms ts
   | As srt ->
       fprintf ppf "@[<4>(as@ %a@ %a)@]" pr_term t pr_sort srt *)

let print_term out_ch t =
  fprintf (formatter_of_out_channel out_ch) "%a@?" pr_term t

let rec pr_adt_args ppf = function
  | [] -> ()
  | (id, srt) :: args ->
      fprintf ppf "@ (%a@ %a)%a" pr_smt_ident id pr_sort srt pr_adt_args args

let rec pr_adt_constrs ppf = function
  | [] -> ()
  | (id, args) :: cnstrs ->
      fprintf ppf "@ (%a%a)%a" pr_smt_ident id pr_adt_args args pr_adt_constrs
        cnstrs

(* let rec pr_adts ppf = function
   | [] -> ()
   | (id, cnstrs) :: adts ->
       fprintf ppf "@ (%a%a)%a" pr_smt_ident id pr_adt_constrs cnstrs pr_adts adts *)

let rec pr_adt ppf (id, params, constrs) =
  match params with
  | [] -> fprintf ppf "@[%a (%a)@]" pr_smt_ident id pr_adt_constrs constrs
  | _ ->
      fprintf ppf "@[%a (par (%a) (%a))@]" pr_smt_ident id pr_smt_idents params
        pr_adt_constrs constrs

let rec pr_adts ppf adt_list =
  let id_list, params_list, constr_list = List.unzip3 adt_list in

  let pr_sorts ppf (id, params) = fprintf ppf "(%a %i)" pr_smt_ident id (List.length params) in

  let pr_constrs ppf (params, constrs) = match params with
  | [] -> fprintf ppf "@[(%a)@]" pr_adt_constrs constrs
  | _ ->
      fprintf ppf "@[(par (%a) (%a))@]" pr_smt_idents params
        pr_adt_constrs constrs
  in

  fprintf ppf "(%a) (%a)" (Util.Print.pr_list_sep " " pr_sorts) (List.zip_exn id_list params_list) (Util.Print.pr_list_sep " " pr_constrs) (List.zip_exn params_list constr_list)

  

let pr_command ppf = function
  | SetInfo (i, v, _) -> fprintf ppf "@[<10>(set-info@ %s@ %s)@]@," i v
  | SetOption (o, v, _) -> fprintf ppf "@[<12>(set-option@ %s@ %s)@]@," o v
  | SetLogic (l, _) -> fprintf ppf "@[<11>(set-logic@ %s)@]@," l
  | DeclareSort (id, n, _) ->
      fprintf ppf "@[<14>(declare-sort@ %a@ %d)@]@," pr_smt_ident id n
  | DeclareDatatype (adt, _) ->
      fprintf ppf "@[<19>(declare-datatype@ @[<2>%a@])@]@," pr_adt adt
  | DeclareDatatypes (adts, _) ->
      fprintf ppf "@[<19>(declare-datatypes@ @[<2>%a@])@]@," pr_adts adts
  | DefineSort (id, svs, srt, _) ->
      fprintf ppf "@[<13>(define-sort@ %a@ (%a)@ %a)@]@," pr_smt_ident id pr_smt_idents
        svs pr_sort srt
  | DeclareFun (id, srts, srt, _) ->
      fprintf ppf "@[<13>(declare-fun@ %a@ @,(%a)@ %a)@]@," pr_smt_ident id pr_sorts
        srts pr_sort srt
  | DeclareConst (id, srt, _) ->
      fprintf ppf "@[<13>(declare-const@ %a@ %a)@]@," pr_smt_ident id pr_sort srt
  | DefineFun (id, vs, srt, t, _) ->
      fprintf ppf "@[<12>(define-fun@ %a@ (%a)@ %a@ %a)@]@," pr_smt_ident id
        pr_var_decls vs pr_sort srt pr_term t
  | DefineFunRec (id, vs, srt, t, _) ->
      fprintf ppf "@[<12>(define-fun-rec@ %a@ (%a)@ %a@ %a)@]@," pr_smt_ident id
        pr_var_decls vs pr_sort srt pr_term t
  (* | DefineFunsRec (defs, _) ->
      fprintf ppf "@[<12>(define-funs-rec@ @[<2>(%a)@])@]@," pr_list_pair_of_terms defs *)
  | Assert (t, _) ->
      fprintf ppf "@[<4>(assert@ (! %a :named %a))@]@," pr_term t Ident.pr
        (Ident.fresh Loc.dummy "$hyp$")
  | Push (n, _) -> fprintf ppf "@[<6>(push@ %d)@]@," n
  | Pop (n, _) -> fprintf ppf "@[<5>(pop@ %d)@]@," n
  | CheckSat _ -> fprintf ppf "@[(check-sat)@]@."
  | GetModel _ -> fprintf ppf "(get-model)@."
  | GetUnsatCore _ -> fprintf ppf "(get-unsat-core)@,"
  | Exit _ -> fprintf ppf "(exit)@,"

let print_comment out_ch cmnt =
  fprintf
    (formatter_of_out_channel out_ch)
    "@[<v>; %s @,@]@?"
    (String.substr_replace_all cmnt ~pattern:"\n" ~with_:"\n; ")

let rec pr_commands ppf = function
  | [] -> ()
  | cmd :: cmds -> fprintf ppf "%a%a" pr_command cmd pr_commands cmds

let print_command out_ch cmds =
  fprintf (formatter_of_out_channel out_ch) "%a@?" pr_command cmds

let print_commands out_ch cmds =
  fprintf (formatter_of_out_channel out_ch) "%a@?" pr_commands cmds
