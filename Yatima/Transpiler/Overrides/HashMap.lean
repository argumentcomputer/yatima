import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides

/-- TODO FIXME: This is very dangerous, assumes that `USize == UInt64`. -/
def Lean.HashMapImp.mkIdx : Override := Override.decl ⟨
  .mkNum `_private.Lean.Data.HashMap 0 ++ `Lean.HashMapImp.mkIdx, ⟦
  (lambda (sz hash h) 
    (let ((u (USize.land hash (- (USize.ofNat sz) 1))))
        (if (< u sz) u 0)))
⟧⟩

def HashMap.module : List Override := [
  Lean.HashMapImp.mkIdx
]

end Overrides

end Lurk

-- #print Lean.HashMapImp
-- _private.Lean.Data.HashMap.0.Lean.HashMapImp.mkIdx