(** The monad of type checking, and its speculative mode. *)

open Base
open Ast

type 'a t = ('a, int) Rewriter.t_ext
(** The monadic type used throughout type-checking below. Type-checking needs one piece of
    pass-local state beyond what [Rewriter.state] carries generically: a depth counter, >
    0 while [ImplicitInstantiation.peek_arg] is speculatively probing an argument that
    might itself be an under-determined implicit functor instantiation (see
    [ImplicitInstantiation.try_resolve_implicit_instantiation]). Rather than adding a
    typing-only field to the shared [Rewriter.state] record -- which every other pass
    (rewrites, atomicity analysis, masks, ...) also carries around for no reason of their
    own -- this is carried in the generic per-pass slot ([state_user_data])
    [Rewriter.t_ext] already reserves for exactly this. Every entry point into this file
    that other files call directly ([process_module], [process_symbol],
    [TypeExpr.expand_type_expr] via [Rewriter.expand_type_expr_ref], the ext_hooks
    callback bundles, ...) still presents a plain unit-state [Rewriter.t] -- see
    [run_typing]/[lift] below and their uses at those boundaries. *)

(** Bridge from this file's internal [t] (speculative-depth state) down to the ambient
    unit-state [Rewriter.t], for use at every externally-visible entry point. The depth
    always starts (and, if callers balance their [peek_arg] entries/exits, ends) at 0. *)
let run_typing (m : 'a t) : 'a Rewriter.t = Rewriter.eval_with_user_state ~init:0 m

(** [run_typing] at the speculative depth [depth], for a callback given to an extension
    while typing at that depth. *)
let run_typing_at (depth : int) (m : 'a t) : 'a Rewriter.t =
  Rewriter.eval_with_user_state ~init:depth m

(** The opposite bridge: lift a foreign, unit-state computation (typically an ext_hooks
    callback, which is deliberately kept ignorant of this file's private speculative-depth
    bookkeeping) into [t], leaving the current depth untouched around it. *)
let lift (m : 'a Rewriter.t) : 'a t =
 fun (s : int Rewriter.state) ->
  let s', a = m { s with Rewriter.state_user_data = () } in
  ({ s' with Rewriter.state_user_data = s.Rewriter.state_user_data }, a)

(** True while inside a [speculatively]-wrapped computation -- see
    [ImplicitInstantiation.peek_arg]. *)
let is_speculative : bool t = fun s -> (s, s.Rewriter.state_user_data > 0)

let speculative_depth : int t = fun s -> (s, s.Rewriter.state_user_data)

(** Run [m] with the speculative-peek depth counter incremented for its duration,
    restoring the enclosing depth on the way out regardless of nesting -- see
    [ImplicitInstantiation.peek_arg]. *)
let speculatively (m : 'a t) : 'a t =
 fun s ->
  let s = { s with Rewriter.state_user_data = s.Rewriter.state_user_data + 1 } in
  let s', a = m s in
  ({ s' with Rewriter.state_user_data = s.Rewriter.state_user_data - 1 }, a)
