import Yatima.Transpiler.Override

namespace Lurk

open Lean.Compiler.LCNF
open Lurk.Backend DSL
open Yatima.Transpiler

namespace Overrides

def not : Override := Override.decl ⟨``not, ⟦
  (lambda (x)
    (let ((_lurk_idx (getelem x 1)))
        (if (= _lurk_idx 0)
            Bool.true
            Bool.false)))
⟧⟩

/-- TODO FIXME: This is a dangerous override because
  we have strict behavior. Try to avoid using this. -/
def and : Override := Override.decl ⟨``and, ⟦
  (lambda (x y)
    (if (eq x Bool.false)
        Bool.false
        y))
⟧⟩

/-- TODO FIXME: This is a dangerous override because
  we have strict behavior. Try to avoid using this. -/
def or : Override := Override.decl ⟨``or, ⟦
  (lambda (x y)
    (if (eq x Bool.true)
        Bool.true
        y))
⟧⟩

/-- TODO FIXME: This is a dangerous override because
  we have strict behavior. Try to avoid using this. -/
def bne : Override := Override.decl ⟨``bne, ⟦
  (lambda (α inst x y)
    (if (eq (inst x y) Bool.true)
        Bool.false
        Bool.true))
⟧⟩

def Bool.module := [
  not, and, or, bne
]

end Overrides

end Lurk