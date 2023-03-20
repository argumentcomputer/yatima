import Yatima.CodeGen.Override

namespace Lurk.Overrides

open Lurk Expr.DSL LDON.DSL DSL
open Yatima.CodeGen

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

end Lurk.Overrides
