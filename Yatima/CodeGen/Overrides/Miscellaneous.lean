import Yatima.CodeGen.Override

namespace Lurk.Overrides

open Lurk Expr.DSL LDON.DSL DSL
open Yatima.CodeGen

def sorryAx : Override := Override.decl ⟨``sorryAx, ⟦
  (throw "sorry")
⟧⟩

def panicCore : Override := Override.decl ⟨``panicCore, ⟦
  (lambda (α inst msg) (throw (str_append "panic! with: " msg)))
⟧⟩

def dbgTrace : Override := Override.decl ⟨``dbgTrace, ⟦
  (lambda (α s f) (begin (emit s) (f Unit.unit)))
⟧⟩

def mixHash : Override := Override.decl ⟨``mixHash, ⟦
  (lambda (x y) (num (commit (cons x y)))) -- TODO this is hackish, but if it works hey it works
⟧⟩

/-- TODO FIXME: This is not strictly needed, but in the future,
  there are optimization oppotunties by flattening `Decidable` to `Bool`
  sooner. This override is currently disabled. -/
def Decidable.decide : Override := Override.decl ⟨``Decidable.decide, ⟦
  (lambda (p h)
    (if (= (getelem h 1) 0)
        Bool.false
        Bool.true))
⟧⟩

def decEq : Override := Override.decl ⟨``decEq, ⟦
  (lambda (α _inst a b) (_inst a b))
⟧⟩

def inferInstanceAs : Override := Override.decl ⟨``inferInstanceAs, ⟦
  (lambda (α i) i)
⟧⟩

def instDecidableNot : Override := Override.decl ⟨``instDecidableNot, ⟦
  (lambda (p dp) (not dp))
⟧⟩

def instBEq : Override := Override.decl ⟨``instBEq, ⟦
  (lambda (α inst) inst)
⟧⟩

def outOfBounds : Override := Override.decl ⟨
  .mkNum `_private.Init.Util 0 ++ `outOfBounds, ⟦
  (lambda (α inst) ("panic!"))
⟧⟩

def Miscellaneous.module := [
  sorryAx,
  panicCore,
  dbgTrace,
  mixHash,
  -- Decidable.decide, -- See the note on `Decidable.decide` override
  decEq,
  inferInstanceAs,
  instDecidableNot,
  instBEq,
  outOfBounds
]

end Lurk.Overrides
