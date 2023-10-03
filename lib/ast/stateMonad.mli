module type StateMonad = sig
  type 'a t

  module Syntax : sig
    val return : 'a -> 'a t
    val bind : 'a t -> ('a -> 'b t) -> 'b t

    val (let+) : 'a t -> ('a -> 'b) -> 'b t
    val (and+) : 'a t -> 'b t -> ('a * 'b) t
    val (let*) : 'a t -> ('a -> 'b t) -> 'b t
    val (and*) : 'a t -> 'b t -> ('a * 'b) t
  end
end