(** The monad of type checking, and its speculative mode. *)

open Base
open Ast

type 'a t = ('a, int) Rewriter.t_ext
(** The monad of type checking. Its state adds a depth to [Rewriter.state], positive while
    an argument is typed speculatively to infer an implicit instantiation (see
    [ImplicitInstantiation.try_resolve_implicit_instantiation]). The depth lives in
    [Rewriter.t_ext]'s per-pass slot, so the entry points of type checking present a plain
    [Rewriter.t] (see [run_typing] and [lift]). *)

(** Runs [m] from depth 0, as a [Rewriter.t]; for the entry points of type checking. *)
let run_typing (m : 'a t) : 'a Rewriter.t = Rewriter.eval_with_user_state ~init:0 m

(** [run_typing] at the speculative depth [depth], for a callback given to an extension
    while typing at that depth. *)
let run_typing_at (depth : int) (m : 'a t) : 'a Rewriter.t =
  Rewriter.eval_with_user_state ~init:depth m

(** Lifts a computation without the depth, such as an extension's callback, into [t]. *)
let lift (m : 'a Rewriter.t) : 'a t =
 fun (s : int Rewriter.state) ->
  let s', a = m { s with Rewriter.state_user_data = () } in
  ({ s' with Rewriter.state_user_data = s.Rewriter.state_user_data }, a)

(** True while inside a [speculatively]-wrapped computation -- see
    [ImplicitInstantiation.peek_arg]. *)
let is_speculative : bool t = fun s -> (s, s.Rewriter.state_user_data > 0)

let speculative_depth : int t = fun s -> (s, s.Rewriter.state_user_data)

(** Runs [m] one speculative level deeper. *)
let speculatively (m : 'a t) : 'a t =
 fun s ->
  let s = { s with Rewriter.state_user_data = s.Rewriter.state_user_data + 1 } in
  let s', a = m s in
  ({ s' with Rewriter.state_user_data = s.Rewriter.state_user_data - 1 }, a)
