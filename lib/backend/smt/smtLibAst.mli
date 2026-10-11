(** SMT-LIBv2 abstract syntax *)

open Ast

type term = Ast.expr
type sort = Ast.Type.t

type smt_ident = qual_ident
and adt_def = smt_ident * smt_ident list * (smt_ident * (smt_ident * sort) list) list
(* name     optional params  (constructor, (destructor, sort) list) list *)

module PreambleConsts : sig
  val loc_ident : smt_ident
  val atomic_token_ident : smt_ident
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
  | DefineFun of smt_ident * (smt_ident * sort) list * sort * term * location option
  | DefineFunRec of smt_ident * (smt_ident * sort) list * sort * term * location option
  (* | DefineFunsRec of (smt_ident * (smt_ident * sort) list * sort * term) list * location option *)
  | Assert of term * smt_ident * location option
  | Push of int * location option
  | Pop of int * location option
  | CheckSat of location option
  | GetModel of location option
  | GetUnsatCore of location option
  | Exit of location option

type sat_result = Sat | Unsat | Unknown

val mk_set_logic : ?loc:location -> string -> command
val mk_set_option : ?loc:location -> string -> string -> command
val mk_set_info : ?loc:location -> string -> string -> command
val mk_declare_sort : ?loc:location -> smt_ident -> int -> command
val mk_declare_datatype : ?loc:location -> adt_def -> command
val mk_declare_datatypes : ?loc:location -> adt_def list -> command
val mk_declare_fun : ?loc:location -> smt_ident -> sort list -> sort -> command
val mk_declare_const : ?loc:location -> smt_ident -> sort -> command
val mk_define_sort : ?loc:location -> smt_ident -> smt_ident list -> sort -> command

val mk_define_fun :
  ?loc:location -> smt_ident -> (smt_ident * sort) list -> sort -> term -> command

val mk_assert : ?loc:location -> ?name:string -> term -> command
val mk_push : ?loc:location -> int -> command
val mk_pop : ?loc:location -> int -> command
val mk_check_sat : ?loc:location -> unit -> command
val mk_get_model : ?loc:location -> unit -> command
val mk_get_unsat_core : ?loc:location -> unit -> command
val mk_exit : ?loc:location -> unit -> command
val pr_smt_ident : Stdlib.Format.formatter -> smt_ident -> unit
val pr_sort : Stdlib.Format.formatter -> sort -> unit
val pr_term : Stdlib.Format.formatter -> term -> unit
val pr_command : Stdlib.Format.formatter -> command -> unit
val pr_comment : Stdlib.Format.formatter -> string -> unit
val command_to_string : command -> string
val comment_to_string : string -> string
