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

  val is_closed : session -> bool
  (** Whether the session was stopped, e.g. after Z3 did not respond in time. *)

  val with_scope : session -> f:(unit -> 'a) -> 'a
  (** Restores the solver scope on return or exception. Cleanup preserves body errors. *)

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

val init : ?logging:bool -> int -> session
(** Starts a solver with a response timeout in milliseconds; zero means unlimited. *)

val stop : session -> unit
(** Closes and reaps the session. Repeated calls are harmless. *)
