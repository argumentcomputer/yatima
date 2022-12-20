import Yatima.Transpiler.Override

namespace Lurk

open Lean.Compiler.LCNF
open Lurk.Backend DSL
open Yatima.Transpiler

namespace Overrides

def ThunkInductiveData : InductiveData :=
  ⟨``Thunk, 0, 0, .ofList [(``Thunk.mk, 0)]⟩

def ThunkCore : Override.Decl := ⟨``Thunk, ⟦
  ,("Thunk" 0 0)
⟧⟩

def Thunk.mk : Override.Decl := ⟨``Thunk.mk, ⟦
  (lambda (α fn) (cons "Thunk" fn))
⟧⟩

def ThunkMkCases (discr : Expr) (alts : Array Override.Alt) : Except String Expr := do
  let #[.alt 0 params k] := alts |
    throw "ThunkMkCases assumes structures having only one alternative, and never produce `default` match, got\n {alts}"
  let #[fn] := params |
    throw s!"`Thunk.mk` case expects exactly 1 param, got\n {params}"
  let fn := fn.toString false
  return .let fn ⟦(cdr $discr)⟧ k

protected def Thunk : Override := Override.ind
  ⟨ThunkInductiveData, ThunkCore, #[Thunk.mk], ThunkMkCases⟩

/-- This is magical, lol -/
def Thunk.pure : Override := Override.decl ⟨``Thunk.pure, ⟦
  (lambda (α a) (Thunk.mk (lambda (unit) a)))
⟧⟩

/-- This is magical, lol -/
def Thunk.get : Override := Override.decl ⟨``Thunk.get, ⟦
  (lambda (self) ((cdr self) Unit.unit))
⟧⟩

def Thunk.module := [
  Lurk.Overrides.Thunk,
  Thunk.pure,
  Thunk.get
]

end Overrides

end Lurk