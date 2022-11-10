import Lurk.Syntax.AST

open Lurk.Syntax AST ToAST
namespace Lurk.Syntax

instance : ToAST Bool where toAST
  | false => .nil
  | true  => .sym "T"

instance [ToAST α] [ToAST β] : ToAST (α × β) where 
  toAST x := ~[toAST x.1, toAST x.1]

instance [ToAST α] [ToAST β] : ToAST (α ⊕ β) where toAST
  | .inl a => toAST a
  | .inr b => toAST b

instance [ToAST α] : ToAST (Option α) where toAST
  | none   => .nil
  | some a => toAST [a] -- Note we can't write `toAST a` here because `a` could be `nil`

end Lurk.Syntax