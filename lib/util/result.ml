open Base
include Result

module Syntax = struct
  let ( let+ ) m f = map m ~f
  let ( let* ) m f = bind m ~f
end
