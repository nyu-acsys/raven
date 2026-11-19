(** [Timeout]: the solver ran out of time; [Inconclusive]: it gave up for another reason,
    such as quantifiers. *)
type validity_result = Valid | Invalid | Inconclusive | Timeout

val parse_sat_result : string -> (SmtLibAst.sat_result, string) result

module SmtSession : sig
  type session

  val write : session -> SmtLibAst.command -> unit
  (** Writes declarations, options, and assertions. Control commands are rejected. *)

  val write_comment : session -> string -> unit
  val assert_expr : ?name:string -> session -> SmtLibAst.term -> unit
  val check_sat : session -> SmtLibAst.sat_result
  val check_valid : ?name:string -> session -> SmtLibAst.term -> validity_result

  val check_valid_with_model :
    ?name:string ->
    session ->
    SmtLibAst.term ->
    model:((SmtLibAst.term list -> Sexplib.Sexp.t list option) -> 'a) ->
    validity_result * 'a option
  (** Like [check_valid], and if the check fails, what [model] makes of the solver's
      model, which it can ask for the values of terms, in their order, as often as it
      needs: a counterexample, certain only for [Invalid]. *)

  val solver_version : session -> string
  (** The solver's version, as it reports it. *)

  val is_closed : session -> bool
  (** Whether the session was stopped. A session that started Z3 itself replaces it when
      it does not respond in time, so that checking goes on; one given its descriptors is
      stopped. *)

  val with_scope : session -> f:(unit -> 'a) -> 'a
  (** Restores the solver scope on return or exception. Cleanup preserves body errors. *)

  type entry
  (** A command written in a scope. *)

  val scoped_commands : session -> f:(unit -> 'a) -> 'a * entry list
  (** Runs [f] in a new scope, returning its result with the commands written in the
      scope, outside nested ones. *)

  val rewrite : session -> entry list -> unit
  (** Writes the commands again, in the current scope, under its current epoch. *)

  val new_epoch : session -> unit
  (** Starts a new epoch: checks no longer assume the assertions of the current one, until
      the current scope is closed. *)

  val keeping : session -> f:(unit -> 'a) -> 'a
  (** Writes the assertions of [f] unguarded by epochs: definitions that cuts keep. *)

  val with_owners : session -> Ast.QualIdent.t list -> f:(unit -> 'a) -> 'a
  (** Writes the commands of [f] as those that declare or axiomatize the symbols [owners].
  *)

  val renew : ?keep:(Ast.QualIdent.t -> bool) -> session -> unit
  (** Resets the solver and replays the session's scopes and commands, so that what the
      checks before left in the solver's search state does not affect the checks after. Of
      the commands written by [with_owners], only those of a symbol in [keep] are
      replayed, also when the solver is replaced later. *)

  module ForTesting : sig
    type read_error =
      | Response_timeout
      | End_of_stream
      | Session_closed
      | Io_error of exn

    val of_owned_descriptors :
      ?pid:int ->
      ?log_out_chan:Stdio.Out_channel.t ->
      response_timeout:float option ->
      input:Unix.file_descr ->
      output:Unix.file_descr ->
      unit ->
      session
    (** Transfers ownership of the descriptors, process, and optional log. *)

    val read_response : session -> (string, read_error) result
    val stack_height : session -> int
  end
end

type session = SmtSession.session

val init : ?logging:bool -> ?cancellation:Util.Diagnostics.cancellation -> int -> session
(** Starts a solver with a response timeout in milliseconds; zero means unlimited. While
    waiting for an answer, it watches the [cancellation] of a server's run. *)

val stop : session -> unit
(** Closes and reaps the session. Repeated calls are harmless. *)
