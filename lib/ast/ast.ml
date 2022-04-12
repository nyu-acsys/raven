(** Abstract syntax tree of a Raven program *)

open Base
open Util
  
type location = Loc.t
    
(** Identifiers *)

let print_debug str = Stdio.Out_channel.output_string Stdio.stdout ("\027[31m" ^ str ^ "\027[0m");

module Ident = struct
  module T = struct
    type t =
        { ident_name: string;
          ident_num: int;
        }
          [@@deriving compare, hash, sexp]

    let to_string id =
      match id.ident_num with
      | 0 -> id.ident_name
      | _ -> Printf.sprintf !"%{String}#%{Int}" id.ident_name id.ident_num
  end

  include T
  include Comparable.Make(T)
  
  let pr ppf id = Stdlib.Format.fprintf ppf "%s" (to_string id)
    
  let pr_list ppf ids = Print.pr_list_comma pr ppf ids

  let make name num = { ident_name = name; ident_num = num }

  let name id = id.ident_name

  let fresh =
    let used_names = Hashtbl.create (module String) in
    fun  ?(id=0) (name : string) ->
    let last_index = 
      Hashtbl.find used_names name |>
      Option.value ~default:(-1)
    in
    let new_max = Int.max (last_index + 1) id in
    Hashtbl.set used_names ~key:name ~data:new_max;
    make name new_max

end

type ident = Ident.t

module IdentMap = Map.M(Ident)
type 'a ident_map = 'a IdentMap.t

(** Qualified identifiers *)

module QualIdent = struct
  module T = struct    
    type t =
      { qual_path: Ident.t list;
        qual_base: Ident.t;
      }
      [@@deriving compare, hash, sexp]
  end

  include T
  include Comparable.Make(T)

  let pr ppf qid =
    Print.pr_list_sep "." Ident.pr ppf (qid.qual_path @ [qid.qual_base])

  let pr_list ppf qids = Print.pr_list_comma pr ppf qids

  let to_string qid = Print.string_of_format pr qid

  let from_ident id = { qual_path = []; qual_base = id }

  let make p id = { qual_path = p; qual_base = id }

  let append qi id = { qual_path = qi.qual_path @ [qi.qual_base]; qual_base = id }
  (* append "M1.M2" "x" -> "M1.M2.x" *)

  let left_append id qi = {qi with qual_path = id :: qi.qual_path}
  (* left_append "M1" "M2.x" -> "M1.M2.x" *)

  (* { qual_path = id :: qi.qual_path; qual_base = qi.qual_base} *)
  
      
end

type qual_ident = QualIdent.t

module QualIdentMap = Map.M(QualIdent)
type 'a qual_ident_map = 'a QualIdentMap.t

(** Types *)

module Type = struct
  
  type type_attr =
      { type_loc: Loc.t [@hash.ignore] [@compare.ignore]; }
 
  and var_decl =
    { var_name : Ident.t;
      var_loc : location [@hash.ignore] [@compare.ignore];
      var_type : t;
      var_const : bool;
      var_ghost : bool;
      var_implicit : bool;
    } [@@deriving compare, hash]

  and variant_decl =
      { variant_name : Ident.t;
        variant_loc : location [@hash.ignore] [@compare.ignore];
        variant_args : var_decl list;
      }
        
  and t =
    | Int
    | Bool
    | Unit
    | AnyRef
    | Perm
    | Bot
    | Any
    | Var of QualIdent.t
    | Set
    | Map
    | Struct of var_decl list
    | Data of variant_decl list
    | App of t * t list * type_attr
  (*| TypeData of qual_ident * type_attr*)
    | Dot of t * Ident.t * type_attr
    [@@deriving compare, hash]

          
  (** Pretty printing types *)        
          
  let ref_type_string = "Ref"
  let map_type_string = "Map"
  let set_type_string = "Set"
  let bool_type_string = "Bool"
  let int_type_string = "Int"
  let unit_type_string = "Unit"
  let perm_type_string = "Perm"
  let bot_type_string = "Bot"
  let any_type_string = "Any"
  let anyref_type_string = "AnyRef"
  let struct_type_string = "struct"
  let data_type_string = "struct"
      
  let to_name = function
  | Int -> int_type_string
  | Bool -> bool_type_string
  | Unit -> unit_type_string
  | Bot -> bot_type_string
  | Any -> any_type_string
  | AnyRef -> anyref_type_string
  | Set -> set_type_string
  | Map -> map_type_string
  | Perm -> perm_type_string
  | Struct _ -> struct_type_string
  | Data _ -> data_type_string
  | Var id -> QualIdent.to_string id
  | App _ -> "App"
  | Dot _ -> "Dot"
      
  let rec pr ppf t = match t with
  | Int
  | Bool
  | Unit
  | Any
  | Bot
  | AnyRef
  | Perm
  | Var _
  | Set
  | Map ->  Stdlib.Format.fprintf ppf "%s" (to_name t)
  | Struct decls ->
      Stdlib.Format.fprintf ppf "struct {@\n  @[%a@]@\n}"
        pr_var_decl_list decls
  | Data decls ->
      Stdlib.Format.fprintf ppf "data {@\n  @[%a@]@\n}"
        pr_variant_decl_list decls
  | App (t1, [], _) -> pr ppf t1
  | App (t1, ts, _) ->
      Stdlib.Format.fprintf ppf "%a[@[%a@]]" pr t1 (Print.pr_list_comma pr) ts
  | Dot (t1, id, _) ->
      Stdlib.Format.fprintf ppf "%a.%a" pr t1 Ident.pr id
  and pr_var_decl ppf decl =
    let open Stdlib.Format in
    fprintf ppf "%s%s @[<2>%a@ :@ %a@]"
      (if decl.var_ghost then "ghost " else "")
      (if decl.var_const then "val" else "var")
      Ident.pr decl.var_name
      pr decl.var_type
  and pr_var_decl_list ppf =
    Print.pr_list_nl pr_var_decl ppf
  and pr_variant_decl ppf decl =
    let open Stdlib.Format in
    fprintf ppf "case %a(@[%a@])"
      Ident.pr decl.variant_name
      pr_arg_list decl.variant_args
  and pr_variant_decl_list ppf =
    Print.pr_list_nl pr_variant_decl ppf
  and pr_ident ppf (id, t) =
    Stdlib.Format.fprintf ppf "%a:@ %a" Ident.pr id pr t
  and pr_arg_list ppf =
    Print.pr_list_comma (fun ppf decl -> pr_ident ppf (decl.var_name, decl.var_type)) ppf 

      
  let pr_list ppf ts =
    Print.pr_list_comma pr ppf ts
        

  let to_string t = Print.string_of_format pr t
      
  (** Constructors *)

  let dummy_attr = { type_loc = Loc.dummy }
        
  let mk_attr loc =
    if Loc.(loc = dummy)
    then dummy_attr
    else { type_loc = loc }

  let mk_app ?(loc=Loc.dummy) t ts = App (t, ts, mk_attr loc)
  let mk_dot ?(loc=Loc.dummy) t id = Dot (t, id, mk_attr loc)
        
  let mk_int loc = App (Int, [], mk_attr loc)
  let mk_bool loc = App (Bool, [], mk_attr loc)
  let mk_unit loc = App (Unit, [], mk_attr loc)
  let mk_any loc = App (Any, [], mk_attr loc)
  let mk_anyref loc = App (AnyRef, [], mk_attr loc)
  let mk_set loc = App (Set, [], mk_attr loc)
  let mk_map loc = App (Map, [], mk_attr loc)
  let mk_perm loc = App (Perm, [], mk_attr loc)
  let mk_struct decls = Struct decls
  let mk_data decls = Data decls
  let mk_var loc qid = App (Var qid, [], mk_attr loc)

  (** Subtyping *)
      
  let rec join t1 t2 =
    match t1, t2 with
    | Bot, t | t, Bot -> t
    | Bool, Perm | Perm, Bool -> Perm
    | AnyRef, Struct _ | Struct _, AnyRef -> AnyRef
    | App (t1, [], a1), App (t2, [], _) ->
        App (join t1 t2, [], a1)
    | _ -> Any

   (** Auxiliary utility functions *)

   let is_ghost_var vdecl = vdecl.var_ghost         
   let is_const_var vdecl = vdecl.var_const
   let is_implicit_var vdecl = vdecl.var_implicit

end

type type_expr = Type.t

type var_decl = Type.var_decl
      
(** Expressions *)
          
module Expr = struct

  type constr =
    (* Constants *)
    | Null
    | Unit
    | Bool of bool
    | Int of Int64.t
    | Empty
    (* Unary operators *)
    | Not | Uminus
    (* Binary operators *)
    | Eq | Gt | Lt | Geq | Leq
    | Diff | Union | Inter | Elem | Subseteq
    | And | Or | Impl
    | Plus | Minus | Mult | Div | Mod
    | Dot | Call | Read
    (* Ternary operators *)
    | Ite | Write | Own
    (* Variable arity operators *)
    | Setenum
    | Var of qual_ident
    | New of type_expr
      
  type binder =
    | Forall | Exists | Compr

  
      
  type expr_attr =
      { expr_loc: location;
        expr_type: type_expr;
      }
        
  and t =
    (* Application expressions *)
    | App of constr * t list * expr_attr
    (* Variable binder expressions *)
    | Binder of binder * var_decl list * t * expr_attr

  let mk_attr loc t =
    { expr_loc = loc; expr_type = t; }
          
  let attr_of = function
    | App (_, _, attr)
    | Binder (_, _, _, attr) -> attr
          
  let loc t = t |> attr_of |> (fun attr -> attr.expr_loc)
          
  let to_type t = t |> attr_of |> (fun attr -> attr.expr_type)
          
  (** Pretty printing expressions *)

  let constr_to_string = function
  (* function symbols *)
  | Bool b -> Printf.sprintf "%b" b
  | Int i -> Int64.to_string i
  | Null -> "null"
  | Unit -> "()"
  | Dot -> "."
  | Call -> "call"
  | Read -> "read"
  | Write -> "write"
  | Uminus -> "-"
  | Plus -> "+"
  | Minus -> "-"
  | Mult -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Empty -> "{||}"
  | Setenum -> "{||}"
  | Union -> "++"
  | Inter -> "**"
  | Diff -> "--"
  | Ite -> "ite"
  | New t -> Printf.sprintf !"new %{Type}" t
  (* predicate symbols *)
  | Eq -> "=="
  | Leq -> "<="
  | Geq -> ">="
  | Lt -> "<"
  | Gt -> ">"
  | Elem -> "in"
  | Subseteq -> "subsetof"
  | And -> "&&"
  | Not -> "!"
  | Or -> "||"
  | Impl -> "==>"
  (* variables / uninterpreted symbols *)
  | Var id -> QualIdent.to_string id
  (* ownership predicates *)
  | Own -> "own"      
            
  let pr_constr ppf c = Stdlib.Format.fprintf ppf "%s" (constr_to_string c)
  
  let constr_to_prio = function
    | Null | Unit | Empty | Int _ | Bool _ -> 0
    | Dot | Setenum | Read | Write | Own | Var _ -> 1
    | Uminus | Not -> 2
    | Call | New _ -> 3
    | Mult | Div | Mod -> 4
    | Minus | Plus -> 5
    | Diff | Union | Inter -> 6
    | Gt | Lt | Geq | Leq | Elem | Subseteq -> 7
    | Eq -> 8
    | And -> 12
    | Or | Impl -> 16
    | Ite -> 17
          
  let to_prio = function
    | App (c, _, _) -> constr_to_prio c
    | Binder (Compr, _, _, _) -> 0
    | Binder ((Forall | Exists), _, _, _) -> 18

  let binder_to_string = function
    | Exists -> "exists"
    | Forall -> "forall"
    | Compr -> "%compr%"
          
  let rec pr ppf e =
    let open Stdlib.Format in
    match e with
    | App (And, [], a) -> pr ppf (App (Bool false, [], a))
    | App (Or, [], a) -> pr ppf (App (Bool true, [], a))
    | App ((Union | Setenum), [], a) -> pr ppf (App(Empty, [], a))
    | App (Inter, [], _) -> fprintf ppf "Univ"
    | App (c, [], _) -> fprintf ppf "%a" pr_constr c
    | App (Call, e :: es, _) ->
        fprintf ppf "%a(@[%a@])" pr e pr_list es
    | App (Dot, [e2; e1], _) | App (Read, [e1; e2], _) ->
        fprintf ppf "%a.%a" pr e2 pr e1
    | App (Write, [e1; e2; e3], _) ->
      fprintf ppf "%a[|%a@ :=@ %a|]" pr e1 pr e2 pr e3
    | App ((Minus | Plus | Mult | Div | Mod | Diff | Inter | Union
            | Eq | Subseteq | Leq | Geq | Lt | Gt | Elem | And | Or | Impl as c), [e1; e2], _) ->
      let pr_e1 = 
        if constr_to_prio c < to_prio e1
        then pr_paran
        else pr
      in
      let pr_e2 =
        if constr_to_prio c <= to_prio e2
        then pr_paran
        else pr
      in        
      fprintf ppf "@[<2>%a %a@ %a@]" pr_e1 e1 pr_constr c pr_e2 e2
  | App (Setenum, es, _) -> 
      fprintf ppf "{|@[%a@]|}" pr_list es
  | App (c, es, _) -> fprintf ppf "%a(@[%a@])" pr_constr c pr_list es
  | Binder (b, vs, e1, _) ->
      fprintf ppf "@[%a@]" pr_binder (b, vs, e1, to_type e)
  and pr_list ppf = Print.pr_list_comma pr ppf 
  and pr_paran ppf = Stdlib.Format.fprintf ppf "(%a)" pr
  and pr_binder ppf = function
    | ((Forall | Exists as b), vs, e, _) ->
        Stdlib.Format.fprintf ppf "%s@ %a@ ::@ %a" (binder_to_string b) pr_var_decl_list vs pr e
    | (Compr, vs, e, App (Set, _, _)) ->
        Stdlib.Format.fprintf ppf "{|@ @[%a@ ::@ %a@]@ |}" pr_var_decl_list vs pr e
    | (Compr, vs, e, _) ->
        Stdlib.Format.fprintf ppf "[|@ @[%a@ ::@ %a@]@ |]" pr_var_decl_list vs pr e 
  and pr_var_decl ppf vdecl =
    let open Type in
    Stdlib.Format.fprintf ppf "%s%s%a"
      (if vdecl.var_implicit then "implicit" else "")
      (if vdecl.var_ghost then "ghost" else "")
      Type.pr_ident (vdecl.var_name, vdecl.var_type)
  and pr_var_decl_list ppf =
    Print.pr_list_comma pr_var_decl ppf

  let to_string e = Print.string_of_format pr e

  (** Constructors *)

  let mk_app ?(loc=Loc.dummy) ?(typ=Type.Any) c es =
    App (c, es, mk_attr loc typ)

  let mk_binder ?(loc=Loc.dummy) ?(typ=Type.Any) b vs e =
    Binder (b, vs, e, mk_attr loc typ)

  let mk_bool ?(loc=Loc.dummy) b =
    mk_app ~loc ~typ:Type.Bool (Bool b) []
      
  (** Constructor for conjunction.*)
  let mk_and ?(loc=Loc.dummy) =
    function
      | [] -> mk_bool ~loc false
      | [e] -> e
      | es ->
          let t = List.fold_left es ~init:Type.Bool ~f:(fun t e -> Type.join t (to_type e)) in
          mk_app ~loc ~typ:t And es

  (** Constructor for disjunction.*)
  let mk_or ?(loc=Loc.dummy) =
    function
      | [] -> mk_bool ~loc true
      | [e] -> e
      | es ->
          let t = List.fold_left es ~init:Type.Bool ~f:(fun t e -> Type.join t (to_type e)) in
          mk_app ~loc ~typ:t Or es

end

type expr = Expr.t

      
(** Statements *)

module Stmt = struct
  
  type spec =
      { spec_form: expr;
        spec_atomic: bool;
        spec_name: string;
        spec_error: (qual_ident -> (string * string)) option;
      }

  type var_def =
      { var_decl : var_decl;
        var_init : expr option;
      }

  type new_desc =
      { new_lhs: ident;
        new_type: type_expr;
        new_args: expr list;
      }

  type assign_desc =
      { assign_lhs: expr list;
        assign_rhs: expr;
      }
        
  type call_desc =
      { call_lhs: qual_ident list;
        call_name: qual_ident;
        call_args: expr list;
      }
  
  type fold_desc =
      { fold_expr: expr;
      }

  type unfold_desc =
      {
        unfold_expr: expr;
      }

  type basic_stmt_desc =
    | VarDef of var_def
    | Assume of spec
    | Assert of spec
    | New of new_desc
    | Assign of assign_desc
    | Havoc of expr list
    | Call of call_desc
    | Return of expr list
    | Fold of fold_desc
    | Unfold of unfold_desc
        
  type t =
      { stmt_desc: stmt_desc;
        stmt_loc: location;
      }

  and loop_desc =
      { loop_contract: spec list; (** the loop invariant *)
        loop_prebody: t; (** the statement executed before testing the loop condition *)
        loop_test: expr; (** the loop condition *)
        loop_postbody: t; (** the actual loop body *)
      }
      
  and cond_desc =
      { cond_test: expr;
        cond_then: t;
        cond_else: t;
      }

  and ghost_desc = 
      {
        ghost_body: t list;
      }  
      
  and stmt_desc =
    | Block of t list
    | Basic of basic_stmt_desc
    | Loop of loop_desc
    | Cond of cond_desc
    | Ghost of ghost_desc

  (** Pretty printing statements *)
          
  let pr_var_def ppf vdef =
    let open Stdlib.Format in
    fprintf ppf "%s%s @[<2>%a@ :@ %a%a@]"
      (if Type.is_ghost_var vdef.var_decl then "ghost " else "")
      (if Type.is_const_var vdef.var_decl then "val" else "var")
      Ident.pr vdef.var_decl.var_name
      Type.pr vdef.var_decl.var_type
      (fun ppf -> function
        | Some e -> fprintf ppf "@ =@ %a" Expr.pr e
        | None -> ()) vdef.var_init
          
  let rec pr_spec_list stype ppf =
    let open Stdlib.Format in
    function
      | [] -> ()
      | [sf] -> 
          fprintf ppf "%s%s@[<2>@ %a@]"
            (if sf.spec_atomic then "atomic " else "")
            stype
            Expr.pr sf.spec_form
      | sf :: sfs -> 
          fprintf ppf "@<0>%s%s@[<2>@ %a@]@\n%a"
            (if sf.spec_atomic then "atomic " else "")
            stype
            Expr.pr sf.spec_form
            (pr_spec_list stype) sfs
            
  let pr_basic_stmt ppf =
    let open Stdlib.Format in
    function
      | VarDef vdef ->
          pr_var_def ppf vdef
      | Assign astm ->
          (match astm.assign_lhs with
          | [] -> Expr.pr ppf astm.assign_rhs
          | es ->
              fprintf ppf "@[<2>%a@ :=@ %a@]" 
                Expr.pr_list es
                Expr.pr astm.assign_rhs)
      | Havoc es -> 
          fprintf ppf "@[<2>havoc@ %a@]" Expr.pr_list es
      | New nstm ->
          (match nstm.new_args with
          | [] ->
              fprintf ppf "@[<2>%a@ :=@ new@ %a@]" 
                Ident.pr nstm.new_lhs 
                Type.pr nstm.new_type
          | args ->
              fprintf ppf "@[<2>%a@ :=@ new@ %a(%a)@]" 
                Ident.pr nstm.new_lhs 
                Type.pr nstm.new_type
                Expr.pr_list args)
      | Assume sf ->
          pr_spec_list "assume" ppf [sf]
      | Assert sf ->
          pr_spec_list "assert" ppf [sf]
      | Fold fld ->
          fprintf ppf "@[<2>fold %a@]" 
            Expr.pr fld.fold_expr
      | Unfold ufld ->
          fprintf ppf "@[<2>unfold %a@]" 
            Expr.pr ufld.unfold_expr
      | Return es -> 
          fprintf ppf "@[<2>return@ %a@]" Expr.pr_list es
      | Call cstm -> 
          match cstm.call_lhs with
          | [] ->
              fprintf ppf "@[%a(@[%a@])@]" 
                QualIdent.pr cstm.call_name 
                Expr.pr_list cstm.call_args
          | _ ->
              fprintf ppf "@[<2>%a@ :=@ @[%a(@[%a@])@]@]" 
                QualIdent.pr_list cstm.call_lhs 
                QualIdent.pr cstm.call_name 
                Expr.pr_list cstm.call_args

                

  let rec pr ppf stmt =
    let open Stdlib.Format in
    match stmt.stmt_desc with
    | Loop ldesc ->
        fprintf ppf "%awhile (%a)@ @,@[<2>@ @ %a@]@\n%a" 
          (fun ppf -> function
            | { stmt_desc = Block []; _} -> ()
            | s -> pr ppf s) ldesc.loop_prebody
          Expr.pr ldesc.loop_test 
          (pr_spec_list "invariant") ldesc.loop_contract
          pr ldesc.loop_postbody
    | Cond cdesc ->
        (match cdesc.cond_else.stmt_desc with
        | Block [] ->
            fprintf ppf "if (@[%a@]) %a"
              Expr.pr cdesc.cond_test
              pr cdesc.cond_then
        | _ ->
            fprintf ppf "if (@[%a@]) %a@ else@ %a"
              Expr.pr cdesc.cond_test
              pr cdesc.cond_then
              pr cdesc.cond_else)
    | Block stmts ->
        (match stmts with
        | [] -> fprintf ppf "{ }"
        | _ -> fprintf ppf "{@\n  @[%a@]@\n}" pr_block stmts)
    | Basic bs ->
        pr_basic_stmt ppf bs
    | Ghost gdesc ->
        fprintf ppf "{!@\n  @[%a@]@\n!}"
          pr_block gdesc.ghost_body

  and pr_block ppf stmts = Print.pr_list_nl pr ppf stmts

  let to_string s = Print.string_of_format pr s

  let print chan s = Print.print_of_format pr s chan
      
  (** Constructors *)

  let mk_skip loc =
    { stmt_desc = Block [];
      stmt_loc = loc;
    }
      
end
            
(** Callable units (functions, procedures, ...) *)
    
module Callable = struct

  type call_kind =
    | Proc | Lemma | Func | Pred
        
  type call_decl =
      { call_decl_kind: call_kind; (** kind of declaration *)
        call_decl_name: ident; (** name of associated declaration *)
        call_decl_formals: ident list;  (** formal parameter list *)
        call_decl_returns: ident list; (** return parameter list *)
        call_decl_locals: var_decl ident_map; (** all local variables *)    
        call_decl_precond: Stmt.spec list; (** precondition *)
        call_decl_postcond: Stmt.spec list; (** postcondition *)
        call_decl_loc: location; (** source location of declaration *)
      }

  type proc_def =
      { proc_decl: call_decl;
        proc_body: Stmt.t option;
      }

  type func_def =
      { func_decl: call_decl;
        func_body: expr option;
      }

  type t =
    | FuncDef of func_def
    | ProcDef of proc_def
        
  let pr_call_decl_specs ppf call_decl =
    let open Stdlib.Format in
    let pr_specs stype ppf = function
      | [] -> ()
      | specs -> fprintf ppf "@\n%a" (Stmt.pr_spec_list stype) specs
    in
    fprintf ppf "%a%a"
      (pr_specs "requires") call_decl.call_decl_precond
      (pr_specs "ensures") call_decl.call_decl_postcond

  let pr_call_decl ppf call_decl =
    let open Stdlib.Format in
    let lookup = List.map ~f:(Map.find_exn call_decl.call_decl_locals) in
    let kind =
      match call_decl.call_decl_kind with
      | Pred -> "pred"
      | Func -> "func"
      | Proc -> "proc"
      | Lemma -> "lemma"
    in
    let pr_returns ppf = function
      | [] -> ()
      | rs ->
          fprintf ppf "@\nreturns (@[<0>%a@])"
            Expr.pr_var_decl_list (lookup rs)
    in
    fprintf ppf "@[<2>%s %a(@[<0>%a@])%a%a@]"
      kind
      Ident.pr call_decl.call_decl_name
      Expr.pr_var_decl_list (lookup call_decl.call_decl_formals)
      pr_returns call_decl.call_decl_returns
      pr_call_decl_specs call_decl

  let pr ppf def =
    let open Stdlib.Format in
    let pr_proc_body pr_body' ppf = function
      | Some e ->
          fprintf ppf "@\n@[<1> %a@]" pr_body' e 
          (* Todo: make this work properly by removing the extra space.  *)
      | None -> fprintf ppf "@\n"
    in
    let pr_fn_body pr_body' ppf = function
      | Some e ->
          fprintf ppf "@\n{@[<1>@\n%a@]@\n}" pr_body' e
      | None -> fprintf ppf "@\n"
    in

    match def with
    | FuncDef fdef ->
        fprintf ppf "%a%a" pr_call_decl fdef.func_decl (pr_fn_body Expr.pr) fdef.func_body
    | ProcDef pdef ->
        fprintf ppf "%a%a" pr_call_decl pdef.proc_decl (pr_proc_body Stmt.pr) pdef.proc_body
    
end
  
(** Modules *)

module Module = struct
    
  type type_alias =
      { type_alias_name: ident;
        type_alias_def: type_expr option;
        type_alias_rep: bool;
        type_alias_loc: location;
      }
        
  type module_alias =
      { mod_alias_name: ident;
        mod_alias_type: type_expr;
        mod_alias_def: type_expr option;
        mod_alias_loc: location;
      }

  type module_decl =
      { mod_decl_name: ident;
        mod_decl_formals: ident list;
        mod_decl_returns: type_expr list;
        mod_decl_rep: ident option;
        mod_decl_mod_defs: module_decl ident_map;
        mod_decl_mod_aliases: module_alias ident_map;
        mod_decl_types: type_alias ident_map;
        mod_decl_callables: Callable.call_decl ident_map;
        mod_decl_vars: var_decl ident_map;
        mod_decl_loc: location;
      }
       
  type import_directive =
    | ModImport of type_expr
    | MemImport of qual_ident
          
  type member_def =
    | TypeAlias of type_alias
    | Import of import_directive
    | ModDef of module_def
    | ValDef of Stmt.var_def
    | CallDef of Callable.t

  and module_def =
    | ModImpl of t
    | ModAlias of module_alias
          
  and t =
      { mod_decl: module_decl;
        mod_def: member_def list;
        mod_interface: bool;
      }

  let rec pr ppf md =
    let open Stdlib.Format in
    let mod_vs =
      List.map md.mod_decl.mod_decl_formals
        ~f:(fun v -> v, (Map.find_exn md.mod_decl.mod_decl_mod_aliases v).mod_alias_type)
    in
    fprintf ppf "@[<2>%s@ %a%a%a@]@\n{@[<1>@\n%a@]@\n}"
      (if md.mod_interface then "interface" else "module")
      Ident.pr md.mod_decl.mod_decl_name
      (* formal parameters *)
      (fun ppf -> function
        | [] -> ()
        | vs -> fprintf ppf "[@[%a@]]" (Print.pr_list_comma Type.pr_ident) vs
      ) mod_vs
      (* return types *)
      (fun ppf -> function
        | [] -> ()
        | vs -> fprintf ppf "@ : %a" Type.pr_list vs
      ) md.mod_decl.mod_decl_returns
      (* body *)
      pr_member_list md.mod_def
  and pr_member ppf = 
    let open Stdlib.Format in
    function
    | TypeAlias ta ->
        fprintf ppf "%stype %a%a"
          (if ta.type_alias_rep then "rep " else "")
          Ident.pr ta.type_alias_name
          (fun ppf -> function
            | None -> ()
            | Some t -> fprintf ppf " = %a" Type.pr t) ta.type_alias_def 
    | Import (ModImport t) ->
        fprintf ppf "@[<2>import@ %a@]" Type.pr t
    | Import (MemImport t) ->
        fprintf ppf "@[<2>import@ %a@]" QualIdent.pr t
    | ModDef (ModImpl md) -> pr ppf md
    | ModDef (ModAlias ma) -> 
        fprintf ppf "@[<2>module@ %a : %a%a@]"
          Ident.pr ma.mod_alias_name
          Type.pr ma.mod_alias_type
          (fun ppf -> function
            | None -> ()
            | Some t -> fprintf ppf " =@ %a" Type.pr t) ma.mod_alias_def 
    | ValDef vdef ->
        Stmt.pr_var_def ppf vdef
    | CallDef cdef -> Callable.pr ppf cdef
  and pr_member_list ppf ms =
    Print.pr_list_sep "@\n@\n" pr_member ppf ms

  let to_string m = Print.string_of_format pr m 

  let print chan m = Print.print_of_format pr m chan
      
  let print_member_list chan ms = Print.print_of_format pr_member_list ms chan


  (** Constructors *)

  let empty_decl =
    { mod_decl_name = Ident.make "" 0;
      mod_decl_formals = [];
      mod_decl_returns = [];
      mod_decl_rep = None;
      mod_decl_mod_defs = Base.Map.empty (module Ident);
      mod_decl_mod_aliases = Base.Map.empty (module Ident);
      mod_decl_types = Base.Map.empty (module Ident);
      mod_decl_callables = Base.Map.empty (module Ident);
      mod_decl_vars = Base.Map.empty (module Ident);
      mod_decl_loc = Loc.dummy;
    }
end
