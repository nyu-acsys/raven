(** External interface to AST-related modules *)

include AstDef

module SymbolTbl = struct
  include SymbolTbl
end

module Rewriter = struct
  include Rewriter
end

module SymbolReference = struct
  include SymbolReference
end

module ProgUtils = struct
  include ProgUtils
end

module Surface = struct
  include Surface
end

module CallGraph = struct
  include CallGraph
end
