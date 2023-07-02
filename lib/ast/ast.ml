(** External interface to AST-related modules *)

include AstDef

module SymbolTbl = struct
  include SymbolTbl
end

module Rewriter = struct
  include Rewriter
end
