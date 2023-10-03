open Base
open AstDef
open Rewriter
open StateMonad

module Traverser (M : StateMonad) = struct
  type 'a t = (state * 'a M.t) -> 

  module Syntax = struct
    (* For ppx_let *)
    module Let_syntax = struct
      let bind m ~f = fun sin ->
        let sout, res = m sin in
        f res sout
  
      let map m ~f = fun sin ->
        let sout, res = m sin in
        (sout, f res)
        
      let both m1 m2 = fun sin ->
        let s1, res1 = m1 sin in
        let s2, res2 = m2 s1 in
        (s2, (res1, res2))
    end
      
    open Let_syntax
    
    let (let+) (m: (state * 'a M.t) -> state * 'a) (f: 'a -> 'b) = ()
    (* : (state -> state * 'b) = map m ~f *)
    let (and+) = both
    let (let* ) (m: state -> state * 'a) (f: 'a -> state -> state * 'b) : (state -> state * 'b) = bind m ~f
    let (and* ) = both
    
  end
end

