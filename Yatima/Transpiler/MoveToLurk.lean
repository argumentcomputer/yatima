import Lurk.Syntax.DSL

namespace Lurk
open Lurk.Syntax AST DSL

instance [ToAST α] [ToAST β] : ToAST (α × β) where
  toAST x := ~[toAST x.1, toAST x.2]

end Lurk