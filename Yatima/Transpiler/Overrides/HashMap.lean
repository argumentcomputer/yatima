import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides

def Lean.HashMapImp.mkIdx : Override := Override.decl ⟨
  .mkNum `_private.Lean.Data.HashMap 0 ++ `Lean.HashMapImp.mkIdx, ⟦
  (lambda (α n v) (List.replicate α n v))
⟧⟩

def HashMap.module : List Override := [
  Lean.HashMapImp.mkIdx
]

end Overrides

end Lurk

-- _private.Lean.Data.HashMap.0.Lean.HashMapImp.mkIdx