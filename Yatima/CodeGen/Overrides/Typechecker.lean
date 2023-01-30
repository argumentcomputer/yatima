import Yatima.CodeGen.Override

namespace Lurk.Overrides

open Lurk.Backend DSL
open Yatima.CodeGen

namespace Yatima.Typechecker

def derefConst : Override := Override.decl ⟨`Yatima.Typechecker.derefConst, ⟦
  (lambda (f store) (open f))
⟧⟩

def module := [
  derefConst
]

end Yatima.Typechecker

end Lurk.Overrides
