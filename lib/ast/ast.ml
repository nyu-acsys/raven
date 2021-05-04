(** Abstract syntax tree of a Raven program *)

open Base
open Util
  
type location = Loc.t
    
(** Identifiers *)

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

  let mk_ident name num = { ident_name = name; ident_num = num }

end

type ident = Ident.t
    
type 'a ident_map = 'a Map.M(Ident).t

(** Qualified identifiers *)

module QualIdent = struct      
  type t =
      { qual_path: Ident.t list;
        qual_base: Ident.t;
      }
      [@@deriving compare, hash]

  let pr ppf qid =
    Print.pr_list_sep "." Ident.pr ppf (qid.qual_path @ [qid.qual_base])

  let pr_list ppf qids = Print.pr_list_comma pr ppf qids

  let to_string qid = Print.string_of_format pr qid

  let from_ident id = { qual_path = []; qual_base = id }

  let make p id = { qual_path = p; qual_base = id }
      
end

type qual_ident = QualIdent.t
      
(** Types *)

module Type = struct
  
  type type_attr =
      { type_loc: Loc.t [@hash.ignore]; }

  and t =
    | Int
    | Bool
    | Unit
    | AnyRef
    | Ref of QualIdent.t
    | Perm
    | Bot
    | Any
    | Var of QualIdent.t
    | Set
    | Map
    | App of t * t list * type_attr
    | Alias of QualIdent.t * t * type_attr
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
  | Ref id
  | Var id
  | Alias (id, _, _) -> QualIdent.to_string id
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
  | Map
  | Alias _
  | Ref _ ->
      Stdlib.Format.fprintf ppf "%s" (to_name t)
  | App (t1, [], _) -> pr ppf t1
  | App (t1, ts, _) ->
      Stdlib.Format.fprintf ppf "%a[@[%a@]]" pr t1 (Print.pr_list_comma pr) ts
  | Dot (t1, id, _) ->
      Stdlib.Format.fprintf ppf "%a.%a" pr t1 Ident.pr id

  let pr_list ppf ts =
    Print.pr_list_comma pr ppf ts
        
  let rec pr_ident ppf (id, t) =
    Stdlib.Format.fprintf ppf "%a:@ %a" Ident.pr id pr t
        
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
  let mk_ref loc qid = App (Ref qid, [], mk_attr loc)
  let mk_var loc qid = App (Var qid, [], mk_attr loc)

  (** Subtyping *)
      
  let rec join t1 t2 =
    match t1, t2 with
    | Bot, t | t, Bot -> t
    | Bool, Perm | Perm, Bool -> Perm
    | AnyRef, Ref _ | Ref _, AnyRef -> AnyRef
    | App (t1, [], a1), App (t2, [], _) ->
        App (join t1 t2, [], a1)
    | _ -> Any
end

type type_expr = Type.t
          
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
      
  type binder =
    | Forall | Exists | Compr

  type var_decl =
      { var_name : ident;
        var_loc : location;
        var_type : type_expr;
        var_const : bool;
        var_ghost : bool;
        var_implicit : bool;
      }
      
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
    | Call -> 3
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
    Stdlib.Format.fprintf ppf "%s%s%a"
      (if vdecl.var_implicit then "implicit" else "")
      (if vdecl.var_ghost then "ghost" else "")
      Type.pr_ident (vdecl.var_name, vdecl.var_type)
  and pr_var_decl_list ppf = Print.pr_list_comma pr_var_decl ppf 
      
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


   (** Auxiliary utility functions *)

   let is_ghost_var vdecl = vdecl.var_ghost         
   let is_const_var vdecl = vdecl.var_const
   let is_implicit_var vdecl = vdecl.var_implicit
   let is_atomic_spec vdecl = vdecl.var_ghost         
            
end

type expr = Expr.t

type var_decl = Expr.var_decl
      
(** Statements *)

module Stmt = struct
  
  type spec =
      { spec_form: expr;
        spec_atomic: bool;
        spec_name: string;
        spec_error: (qual_ident -> (string * string)) option;
      }

  type var_def =
      { var_def_decl : var_decl;
        var_def_init : expr option;
      }

  type new_desc =
      { new_lhs: qual_ident;
        new_type: type_expr;
        new_args: expr list;
      }

  type assign_desc =
      { assign_lhs: qual_ident;
        assign_rhs: expr;
      }
        
  type call_desc =
      { call_lhs: qual_ident list;
        call_name: qual_ident;
        call_args: expr list;
      }

  type basic_stmt_desc =
    | VarDef of var_def 
    | New of new_desc
    | Assign of assign_desc
    | Havoc of qual_ident list
    | Call of call_desc
    | Return of expr list
        
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

  and stmt_desc =
    | Block of t list
    | Basic of basic_stmt_desc
    | Loop of loop_desc
    | Cond of cond_desc

  (** Pretty printing statements *)
          
  let pr_var_def ppf vdef =
    let open Stdlib.Format in
    fprintf ppf "%s%s @[<2>%a@ :@ %a%a@]"
      (if Expr.is_ghost_var vdef.var_def_decl then "ghost " else "")
      (if Expr.is_const_var vdef.var_def_decl then "val" else "var")
      Ident.pr vdef.var_def_decl.var_name
      Type.pr vdef.var_def_decl.var_type
      (fun ppf -> function
        | Some e -> fprintf ppf "@ :=@ %a" Expr.pr e
        | None -> ()) vdef.var_def_init
          
  let pr_basic_stmt ppf =
    let open Stdlib.Format in
    function
      | VarDef vdef ->
          pr_var_def ppf vdef
      | Assign astm -> 
          fprintf ppf "@[<2>%a@ :=@ %a@]" 
            QualIdent.pr astm.assign_lhs 
            Expr.pr astm.assign_rhs
      | Havoc qids -> 
          fprintf ppf "@[<2>havoc@ %a@]" QualIdent.pr_list qids
      | New nstm ->
          (match nstm.new_args with
          | [] ->
              fprintf ppf "@[<2>%a@ :=@ new@ %a@]" 
                QualIdent.pr nstm.new_lhs 
                Type.pr nstm.new_type
          | args ->
              fprintf ppf "@[<2>%a@ :=@ new@ %a(%a)@]" 
                QualIdent.pr nstm.new_lhs 
                Type.pr nstm.new_type
                Expr.pr_list args)
      (*| Assume sf ->
          fprintf ppf "%a@[<2>%sassume@ %a@]"
            pr_comment sf.spec_name
            (fold_spec_form (fun _ -> "pure ") (fun _ -> "") sf)
            pr_spec_form sf
      | Assert sf ->
          fprintf ppf "%a@[<2>%sassert@ %a@]" 
            pr_comment sf.spec_name
            (fold_spec_form (fun _ -> "pure ") (fun _ -> "") sf)
            pr_spec_form sf*)
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
                
  let rec pr_spec_list stype ppf =
    let open Stdlib.Format in
    function
      | [] -> ()
      | [sf] -> 
          fprintf ppf "%s%s[<2>@ %a@]"
            (if sf.spec_atomic then "atomic " else "")
            stype
            Expr.pr sf.spec_form
      | sf :: sfs -> 
          fprintf ppf "@<0>%s%s@[<2>@ %a@]@\n%a"
            (if sf.spec_atomic then "atomic " else "")
            stype
            Expr.pr sf.spec_form
            (pr_spec_list stype) sfs

  let rec pr ppf stmt =
    let open Stdlib.Format in
    match stmt.stmt_desc with
    | Loop ldesc ->
        fprintf ppf "%awhile (%a)@ @,@[<2>@ @ %a@]@\n%a" 
          pr ldesc.loop_prebody 
          Expr.pr ldesc.loop_test 
          (pr_spec_list "invariant") ldesc.loop_contract
          pr ldesc.loop_postbody
    | Cond cdesc ->
        (match cdesc.cond_else.stmt_desc with
        | Block [] ->
            fprintf ppf "if (@[%a@])@ %a"
              Expr.pr cdesc.cond_test
              pr cdesc.cond_then
        | _ ->
            fprintf ppf "if (@[%a@])@ %a@ else@ %a"
              Expr.pr cdesc.cond_test
              pr cdesc.cond_then
              pr cdesc.cond_else)
    | Block stmts ->
        fprintf ppf "{@[<1>@\n%a@]@\n}" pr_block stmts
    | Basic bs ->
        pr_basic_stmt ppf bs

  and pr_block ppf stmts = Print.pr_list_nl pr ppf stmts
          
end
        
(** Modules *)
    
module Module = struct
    
  (** Functions and Procedures *)

  type contr_kind =
    | Proc | Lemma | Func | Pred
        
  type contract =
      { contr_kind: contr_kind; (** kind of declaration *)
        contr_name: ident; (** name of associated declaration *)
        contr_formals: ident list;  (** formal parameter list *)
        contr_returns: ident list; (** return parameter list *)
        contr_locals: var_decl ident_map; (** all local variables *)    
        contr_precond: Stmt.spec list; (** precondition *)
        contr_postcond: Stmt.spec list; (** postcondition *)
    }

  type proc_def =
      { proc_contr: contract;
        proc_body: Stmt.t option;
      }

  type func_def =
      { func_contr: contract;
        func_body: expr option;
      }

  (* Modules *)
      
  type type_alias =
      { type_alias_name: ident;
        type_alias_def: type_expr option;
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
        mod_decl_contracts: contract ident_map;
        mod_decl_vars: var_decl ident_map;
        mod_decl_loc: location;
      }
        
  type import_directive =
    | ModImport of type_expr
    | MemImport of qual_ident
          
  type module_member_def =
    | TypeAlias of type_alias
    | Import of import_directive
    | ModDef of module_def
    | ModAlias of module_alias
    | VarDef of Stmt.var_def
    | FuncDef of func_def
    | ProcDef of proc_def
          
  and module_def =
      { mod_decl: module_decl;
        mod_def: module_member_def list;
        mod_interface: bool;
      }

  let pr_contract_specs ppf contr =
    let open Stdlib.Format in
    fprintf ppf "%a%a"
      (Stmt.pr_spec_list "requires") contr.contr_precond
      (Stmt.pr_spec_list "ensures") contr.contr_postcond

  let pr_contract ppf contr =
    let open Stdlib.Format in
    let lookup = List.map ~f:(Map.find_exn contr.contr_locals) in
    let kind =
      match contr.contr_kind with
      | Pred -> "pred"
      | Func -> "func"
      | Proc -> "proc"
      | Lemma -> "lemma"
    in
    let pr_returns ppf = function
      | [] -> ()
      | rs ->
          fprintf ppf "@\nreturns (@[<0>%a@])@\n"
            Expr.pr_var_decl_list (lookup rs)
    in
    fprintf ppf "@[<2>%s %a(@[<0>%a@])%a%a@]"
      kind
      Ident.pr contr.contr_name
      Expr.pr_var_decl_list (lookup contr.contr_formals)
      pr_returns contr.contr_returns
      pr_contract_specs contr

  let pr_fun_proc_def ppf contr pr_body body =
    let open Stdlib.Format in
    let pr_body ppf = function
      | Some e ->
          fprintf ppf "{@[<1>@\n%a@]@\n}@\n" pr_body e
      | None -> fprintf ppf "@\n"
    in
    fprintf ppf "%a%a" pr_contract contr pr_body body

  let rec pr ppf md =
    let open Stdlib.Format in
    let mod_vs =
      List.map md.mod_decl.mod_decl_formals
        ~f:(fun v -> v, (Map.find_exn md.mod_decl.mod_decl_mod_aliases v).mod_alias_type)
    in
    fprintf ppf "%s@ %a%a%a@ {@[<1>@\n%a@]@\n}"
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
        | vs -> fprintf ppf "@ :@ %a" Type.pr_list vs
      ) md.mod_decl.mod_decl_returns
      (* body *)
      pr_member_list md.mod_def
  and pr_member ppf = 
    let open Stdlib.Format in
    function
    | TypeAlias ta ->
        fprintf ppf "[@<2>type@ %a%a@]"
          Ident.pr ta.type_alias_name
          (fun ppf -> function
            | None -> ()
            | Some t -> fprintf ppf "=@ %a" Type.pr t) ta.type_alias_def 
    | Import (ModImport t) ->
        fprintf ppf "[@<2>import@ %a@]" Type.pr t
    | Import (MemImport t) ->
        fprintf ppf "[@<2>import@ %a@]" QualIdent.pr t
    | ModDef md ->
        pr ppf md
    | ModAlias ma ->
        fprintf ppf "[@<2>module@ %a : %a%a@]"
          Ident.pr ma.mod_alias_name
          Type.pr ma.mod_alias_type
          (fun ppf -> function
            | None -> ()
            | Some t -> fprintf ppf "=@ %a" Type.pr t) ma.mod_alias_def 
    | VarDef vdef ->
        Stmt.pr_var_def ppf vdef
    | FuncDef fdef -> pr_fun_proc_def ppf fdef.func_contr Expr.pr fdef.func_body
    | ProcDef pdef -> pr_fun_proc_def ppf pdef.proc_contr Stmt.pr pdef.proc_body
  and pr_member_list ppf ms =
    Print.pr_list_sep "@\n@\n" pr_member ppf ms
end
