(** The back end: lowering, the generation of verification conditions and their checking
    with an SMT solver. *)

module Lowering = Lowering
module Smt = Smt
module Checker = Checker
module CheckerContext = CheckerContext
module Counterexample = Counterexample
module Dependencies = Dependencies
module Fingerprints = Fingerprints
module SmtPreamble = SmtPreamble
module VerificationCache = VerificationCache
