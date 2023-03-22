import Yatima.CodeGen.Override

namespace Lurk.Overrides

open Lurk Expr LDON DSL
open Yatima.CodeGen

def DecidableInductiveData : InductiveData :=
  ⟨``Decidable, 1, 0, .ofList [(``Decidable.isFalse, 0), (``Decidable.isTrue, 1)]⟩

def DecidableCore : Override.Decl := ⟨``Decidable, ⟦
  (lambda (x) ,("Decidable" 1 0))
⟧⟩

def Decidable.isFalse : Override.Decl := ⟨``Decidable.isFalse, ⟦
  (lambda (p h) Bool.false)
⟧⟩

def Decidable.isTrue : Override.Decl := ⟨``Decidable.isTrue, ⟦
  (lambda (p h) Bool.true)
⟧⟩

def DecidableMkCases (discr : Expr) (alts : Array Override.Alt) : Except String Expr := do
  let mut defaultElse : Expr := .atom .nil
  let mut ifThens : Array (Expr × Expr) := #[]
  for alt in alts do match alt with
    | .default k => defaultElse := k
    | .alt cidx params k =>
      if cidx == 0 then
        let #[h] := params |
          throw s!"`Decidable.isFalse` case expects exactly 1 param, got\n {params}"
        let h := h.toString false
        let case := .mkLet [(h, .nil)] k
        ifThens := ifThens.push (⟦(= _lurk_idx 0)⟧, case)
      else if cidx == 1 then
        let #[h] := params |
          throw s!"`Decidable.isTrue` case expects exactly 1 param, got\n {params}"
        let h := h.toString false
        let case := .mkLet [(h, .nil)] k
        ifThens := ifThens.push (⟦(= _lurk_idx 1)⟧, case)
      else
        throw "{cidx} is not a valid `Decidable` constructor index"
  let cases := Expr.mkIfElses ifThens.toList defaultElse
  return ⟦(let ((_lurk_idx $discr))
            $cases)⟧

protected def Decidable : Override := Override.ind
  ⟨DecidableInductiveData, DecidableCore, #[Decidable.isFalse, Decidable.isTrue], DecidableMkCases⟩

def Decidable.module := [
  Lurk.Overrides.Decidable
]

end Lurk.Overrides
