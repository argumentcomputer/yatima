import Yatima.CodeGen.Override

namespace Lurk.Overrides

open Lurk Expr.DSL LDON.DSL DSL
open Yatima.CodeGen

def BoolInductiveData : InductiveData :=
  ⟨``Bool, 0, 0, .ofList [(``Bool.false, 0), (``Bool.true, 1)]⟩

def BoolCore : Override.Decl := ⟨``Bool, ⟦
  (lambda (x) ,("Bool" 0 0))
⟧⟩

def Bool.false : Override.Decl := ⟨``Bool.false, ⟦
  0
⟧⟩

def Bool.true : Override.Decl := ⟨``Bool.true, ⟦
  1
⟧⟩

def BoolMkCases (discr : Expr) (alts : Array Override.Alt) : Except String Expr := do
  let mut defaultElse : Expr := .atom .nil
  let mut ifThens : Array (Expr × Expr) := #[]
  for alt in alts do match alt with
    | .default k => defaultElse := k
    | .alt cidx params k =>
      if cidx == 0 then
        let #[] := params |
          throw s!"`Bool.false` case expects exactly 0 params, got\n {params}"
        ifThens := ifThens.push (⟦(= _lurk_idx 0)⟧, k)
      else if cidx == 1 then
        let #[] := params |
          throw s!"`Bool.isTrue` case expects exactly 0 params, got\n {params}"
        ifThens := ifThens.push (⟦(= _lurk_idx 1)⟧, k)
      else
        throw s!"{cidx} is not a valid `Bool` constructor index"
  let cases := Expr.mkIfElses ifThens.toList defaultElse
  return ⟦(let ((_lurk_idx $discr))
            $cases)⟧

protected def Bool : Override := Override.ind
  ⟨BoolInductiveData, BoolCore, #[Bool.false, Bool.true], BoolMkCases⟩

def not : Override := Override.decl ⟨``not, ⟦
  (lambda (x)
    (if (eq x Bool.true)
        Bool.false
        Bool.true))
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
  Lurk.Overrides.Bool,
  not, and, or, bne
]

end Lurk.Overrides
