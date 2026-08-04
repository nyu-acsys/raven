(** Configuration and command line options *)

(** Version string *)
let version = "1.2.0"

(** Version of the machine-readable interface an editor integration drives raven
    through: the JSON diagnostic schema emitted under [--lsp-mode], and the flags such
    a client relies on. Deliberately independent of [version] -- a client that can
    fetch and run a raven it was not shipped with needs to know whether it can still
    understand that binary, and most releases change nothing here. Bump it only when
    an existing client would notice the difference. *)
let lsp_protocol_version = 1

(** Oldest Z3 raven is known to work against. A client that supplies its own z3
    alongside a raven it downloaded needs this to tell whether the pair is viable. *)
let min_z3_version = "4.13.0"

(** The command line options *)
let cmd_options_spec = []
