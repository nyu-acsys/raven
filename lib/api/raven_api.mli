(** The interface of Raven for other tools: building programs and verifying them.

    Programs are built as the parser builds them from source: types left to infer are
    inferred by the type checker, and locations, which tools give in terms of their own
    sources, are those Raven reports. *)

val version : int
(** The version of this interface, raised with every change that is not backward
    compatible. *)

(** {1 Building programs} *)

module Loc : sig
  type t

  val make : Lexing.position -> Lexing.position -> t
  (** The range from [start] to [stop], as positions of a lexer such as OCaml's. *)

  val none : t
  (** No location, for constructs without a source. *)

  val start : t -> Lexing.position
  (** The positions a location was made of. *)

  val stop : t -> Lexing.position
end

(** Names, as declared. *)
module Ident : sig
  type t

  val make : loc:Loc.t -> string -> t
end

(** Names, as referred to: [M.N.x] is [Name.make ~loc ~path:["M"; "N"] "x"]. *)
module Name : sig
  type t

  val make : loc:Loc.t -> ?path:string list -> string -> t
  val of_ident : Ident.t -> t
end

module Type : sig
  type t

  val int : loc:Loc.t -> t
  val bool : loc:Loc.t -> t
  val real : loc:Loc.t -> t
  val ref : loc:Loc.t -> t
  val perm : loc:Loc.t -> t

  val infer : loc:Loc.t -> t
  (** A type left to the type checker. *)

  val map : loc:Loc.t -> t -> t -> t
  val set : loc:Loc.t -> t -> t
  val fin_set : loc:Loc.t -> t -> t
  val tuple : loc:Loc.t -> t list -> t

  val named : loc:Loc.t -> Name.t -> t list -> t
  (** The type or module [name], applied to [args] if any, as in [Seq[Int]]. *)

  val atomic_token : loc:Loc.t -> Name.t -> t

  type variant
  (** A variant [case name(args)] of a data type. *)

  val variant : loc:Loc.t -> Ident.t -> (Ident.t * t) list -> variant
  val data : loc:Loc.t -> variant list -> t
end

(** Declarations of parameters, results and bound variables. *)
module Var : sig
  type t

  val make : loc:Loc.t -> ?ghost:bool -> ?implicit:bool -> Ident.t -> Type.t -> t
end

module Expr : sig
  type t

  val pr : Format.formatter -> t -> unit
  (** The expression as Raven source on a caller-owned formatter, without flushing it. *)

  val print : out_channel -> t -> unit
  (** Print to the channel and flush, leaving it open, without adding a newline. *)

  val to_string : t -> string
  (** The expression as Raven source. *)

  val alpha_equal : t -> t -> bool
  (** Whether two expressions are the same up to renaming of their bound variables,
      regardless of locations and type annotations. *)

  val int : loc:Loc.t -> int -> t
  val real : loc:Loc.t -> float -> t
  val bool : loc:Loc.t -> bool -> t
  val null : loc:Loc.t -> t
  val var : loc:Loc.t -> Name.t -> t
  val tuple : loc:Loc.t -> t list -> t

  val annotated : t -> Type.t -> t
  (** [e] annotated with a type, as in [(e: T)]. *)

  val call : loc:Loc.t -> Name.t -> t list -> t
  (** The call of a function, predicate or constructor. *)

  val field : loc:Loc.t -> t -> Name.t -> t
  (** The field of [e], as in [e.f]. *)

  val own : loc:Loc.t -> t list -> t
  val au : loc:Loc.t -> Name.t -> t list -> t
  val au_commit : loc:Loc.t -> Name.t -> t list -> t
  val set : loc:Loc.t -> t list -> t
  val seq : loc:Loc.t -> t list -> t

  val set_compr : loc:Loc.t -> Var.t -> t -> t
  (** The set comprehension [{x: T :: e}]. *)

  val map_literal : loc:Loc.t -> (t * t) list -> t -> t
  (** The map literal [{k1 := v1, ..., else default}]. *)

  val index : loc:Loc.t -> t -> t -> t
  val update : loc:Loc.t -> t -> t -> t -> t
  val slice : loc:Loc.t -> t -> t -> t -> t
  val slice_from : loc:Loc.t -> t -> t -> t
  val slice_to : loc:Loc.t -> t -> t -> t

  val tuple_get : loc:Loc.t -> t -> int -> t
  (** The component [n] of a tuple, as in [e#n]. *)

  val neg : loc:Loc.t -> t -> t
  val not_ : loc:Loc.t -> t -> t

  (** The case of a match: a constructor and the variables bound to its arguments, or the
      default case [_]. Patterns are not nested. *)
  type case = Case of Ident.t * Ident.t list | Default

  val is_ : loc:Loc.t -> t -> Ident.t -> t
  (** [e is c]: whether [e] was built with the constructor [c] of its data type. *)

  val match_ : loc:Loc.t -> t -> (case * t) list -> t
  (** [match e { case c(x, y) => e1 ... }]. *)

  type binop =
    | Mult
    | Div
    | Mod
    | Plus
    | Minus
    | Lt
    | Leq
    | Gt
    | Geq
    | Eq
    | Neq
    | Iff
    | And
    | Or
    | Impl
    | In
    | Not_in
    | Union
    | Inter
    | Diff
    | Subseteq
    | User of string  (** A user-defined symbolic operator. *)

  val binary : loc:Loc.t -> binop -> t -> t -> t
  val ite : loc:Loc.t -> t -> t -> t -> t

  val forall : loc:Loc.t -> ?triggers:t list list -> Var.t list -> t -> t
  (** The quantifiers, with [triggers]. *)

  val exists : loc:Loc.t -> ?triggers:t list list -> Var.t list -> t -> t
end

(** Specifications: assertions, invariants and contract clauses. *)
module Spec : sig
  type t

  val make : ?atomic:bool -> ?name:string -> ?triggers:Expr.t list list -> Expr.t -> t
end

module Stmt : sig
  type t

  type rhs
  (** The right-hand side of an assignment or local definition. *)

  val expr_rhs : Expr.t -> rhs
  (** An expression: assigned to variables, or written to a field or an index if the
      target is one. *)

  val new_rhs : (Name.t * Expr.t option) list -> rhs
  (** An allocation [new(f1: e1, ..., fn)], with initial values of the fields if given. *)

  val local :
    loc:Loc.t ->
    ?ghost:bool ->
    ?const:bool ->
    ?typ:Type.t ->
    ?init:rhs ->
    Ident.t ->
    t list
  (** The local definition [var x: T := rhs], or [val] if [const], with its type left to
      the type checker if none is given. *)

  val assign : loc:Loc.t -> Expr.t list -> rhs -> t

  val bind : loc:Loc.t -> Expr.t list -> Expr.t -> t
  (** The binding [x1, ..., xn :| e]. *)

  val call : loc:Loc.t -> Expr.t -> t
  val spawn : loc:Loc.t -> Name.t -> Expr.t list -> t
  val havoc : loc:Loc.t -> Name.t -> t
  val assert_ : loc:Loc.t -> Spec.t -> t
  val assume : loc:Loc.t -> Spec.t -> t
  val inhale : loc:Loc.t -> Spec.t -> t
  val exhale : loc:Loc.t -> Spec.t -> t
  val return : loc:Loc.t -> Expr.t list -> t

  val fold : loc:Loc.t -> ?witnesses:(Ident.t * Expr.t) list -> Name.t -> Expr.t list -> t
  (** [fold p(args)] and [unfold p(args)], with witnesses or bindings [x := e] of the
      predicate's existentials. *)

  val unfold :
    loc:Loc.t -> ?witnesses:(Ident.t * Expr.t) list -> Name.t -> Expr.t list -> t

  val block : loc:Loc.t -> t list -> t
  val ghost_block : loc:Loc.t -> t list -> t
  val atomic_block : loc:Loc.t -> t list -> t
  val if_ : loc:Loc.t -> Expr.t -> t list -> t list -> t

  val match_ : loc:Loc.t -> Expr.t -> (Expr.case * t list) list -> t
  (** [match e { case c(x, y) => { ... } ... }]: the cases must cover every constructor of
      [e]'s data type, or end with [Default]. *)

  val while_ : loc:Loc.t -> ?invariants:Spec.t list -> Expr.t -> t list -> t
end

module Callable : sig
  type t
  type proc_kind = Proc | Lemma | Axiom

  val proc :
    loc:Loc.t ->
    ?kind:proc_kind ->
    ?atomic:bool ->
    ?auto:bool ->
    ?formals:Var.t list ->
    ?returns:Var.t list ->
    ?requires:Spec.t list ->
    ?ensures:Spec.t list ->
    ?opens:Loc.t * (Name.t * Expr.t list) list ->
    ?decreases:Expr.t list ->
    Ident.t ->
    Stmt.t list option ->
    t
  (** The procedure, lemma or axiom [name] and its body; [atomic] makes a procedure
      physically atomic, so its call counts as one step. It is separate from logically
      atomic [Spec.make ~atomic:true] clauses, which may not be mixed with it. [auto]
      makes a lemma or axiom apply where its postconditions are needed. [opens] lists the
      invariants it may open, with arguments of which trailing ones may be [_];
      [decreases] is the measure that its recursive calls decrease. *)

  type func_kind = Func | Pred | Inv

  val func :
    loc:Loc.t ->
    ?kind:func_kind ->
    ?inline:bool ->
    ?formals:Var.t list ->
    ?returns:Var.t list ->
    ?requires:Spec.t list ->
    ?ensures:Spec.t list ->
    Ident.t ->
    Expr.t option ->
    t
  (** The function, predicate or invariant [name] and its body; [inline] has its uses
      replaced by its body. *)
end

(** The members of modules and programs. *)
module Member : sig
  type t

  val field : loc:Loc.t -> ?ghost:bool -> ?where:Name.t -> Ident.t -> Type.t -> t
  (** The field [name] of type [typ], whose values satisfy the func [where] if given:
      owning the field implies it, and allocations and writes must establish it. *)

  val type_ : loc:Loc.t -> ?rep:bool -> Ident.t -> Type.t option -> t
  (** The type [name], defined as [def] if given, a representation type if [rep]. *)

  val value :
    loc:Loc.t ->
    ?ghost:bool ->
    ?const:bool ->
    ?typ:Type.t ->
    Ident.t ->
    Expr.t option ->
    t
  (** The constant [val name: T = e], or [var] if not [const]. *)

  val callable : Callable.t -> t

  val import : loc:Loc.t -> ?all:bool -> Name.t -> t
  (** [import name], or of all the members of the module [name] if [all]. *)

  val module_ :
    loc:Loc.t ->
    ?interface:bool ->
    ?params:(Ident.t * Name.t) list ->
    ?implements:(Name.t * Type.t list) list ->
    ?sealed:bool ->
    Ident.t ->
    t list ->
    t
  (** The module, or interface if [interface], [name] with parameters [name: I] and the
      interfaces it implements, sealed if [sealed]. *)

  val unit_factory :
    loc:Loc.t ->
    ?interface:bool ->
    ?implements:(Name.t * Type.t list) list ->
    ?sealed:bool ->
    Ident.t ->
    t list ->
    t
  (** The unit-parameter factory [module name() { ... }], or its interface if [interface],
      sealed if [sealed]. *)

  val instance : loc:Loc.t -> ?def:Name.t * Type.t list -> Ident.t -> Name.t -> t
  (** The instance [module name : typ = functor[args]], or the abstract module
      [name : typ] if no definition is given. *)

  val alias : loc:Loc.t -> ?typ:Name.t -> Ident.t -> Name.t -> t
  (** The binding [module name : typ = target], without applying [target]. The declared
      [typ] defaults to [target]. *)

  val unit_instance : loc:Loc.t -> ?typ:Name.t -> Ident.t -> Name.t -> t
  (** The fresh application [module name : typ = factory()]. The declared [typ] defaults
      to [factory]. *)

  val free : t -> t
  (** [member], trusted rather than verified. *)
end

module Program : sig
  type t

  val make : loc:Loc.t -> Member.t list -> t

  val pr : Format.formatter -> t -> unit
  (** The surface program as Raven source on a caller-owned formatter, without flushing
      it. Names outside Raven's source syntax use consistent collision-free aliases in the
      output; the program is unchanged. *)

  val print : out_channel -> t -> unit
  (** Print to the channel and flush, leaving it open, without adding a newline or
      allocating a string containing the whole program. *)

  val to_string : t -> string
  (** The same source as [pr], rendered to a string. *)
end

(** {1 Verifying programs} *)

module Diagnostic : sig
  type severity = Error | Warning

  (** What kind of check reported it. *)
  type kind = Syntax | Type | Verification | Unsupported | Internal | Other

  (** What a verification error says failed. *)
  type code =
    | Assertion
    | Loop_invariant_entry
    | Precondition
    | Postcondition
    | Fold
    | Unfold
    | Permission
    | Frame_preserving_update
    | Bind
    | Injectivity
    | Allocation
    | Commit
    | Abort
    | Uncommitted
    | Atomic_token
    | Implicit_agreement
    | Atomicity
    | Mask
    | Unclosed
    | Invariant_arguments
    | Atomic_update
    | Abortable_call
    | Extension of { extension : string; name : string }
        (** An extension's own check, named by the extension. *)

  val code_name : code -> string
  (** The stable name of [code], as in ["postcondition"] or ["decreases/termination"]. *)

  type related = { related_loc : Loc.t; related_message : string }
  (** A location related to a diagnostic, as a conjunct of a postcondition that may not
      hold, or a counterexample's values. *)

  type t = {
    severity : severity;
    kind : kind;
    code : code option;  (** For verification errors. *)
    loc : Loc.t;
    message : string;
    related : related list;
  }

  val pr : Format.formatter -> t -> unit
  (** The diagnostic as Raven reports it on the command line, without flushing the
      formatter. *)

  val print : out_channel -> t -> unit
  (** Print to the channel and flush, leaving it open, without adding a newline. *)

  val to_string : t -> string
  (** The same diagnostic as [pr], rendered to a string. *)
end

type extension = Default | Eris

type options = {
  extension : extension;
  smt_timeout : int;  (** In milliseconds. *)
  max_errors : int option;  (** No limit if [None]. *)
}

val default_options : options

type result = { verified : bool; diagnostics : Diagnostic.t list }
(** The result of verifying a program: whether it verified, and what Raven reported. *)

val verify : ?options:options -> ?includes:string list -> Program.t -> result
(** Type-checks and verifies [program], together with Raven's library and the files
    [includes], which are trusted as included files are. *)
