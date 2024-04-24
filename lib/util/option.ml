open Base
include Option

let lazy_value ~default = function Some x -> x | None -> default ()
let or_else ~f y = function Some x -> Some x | None -> f y
let map_or_else ~m ~e y = function Some x -> Some (m x) | None -> e y
let flat_map ~f = function Some x -> f x | None -> None
let flat_map_or_else ~m ~e = function Some x -> m x | None -> e ()

module Syntax = struct
  let ( let+ ) m f = map m ~f
  let ( and+ ) = both
  let ( let* ) m f = bind m ~f
  let ( and* ) = both
end
