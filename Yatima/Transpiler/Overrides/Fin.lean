import Yatima.Transpiler.Override

namespace Lurk

open Lean.Compiler.LCNF
open Lurk.Backend DSL
open Yatima.Transpiler

namespace Overrides

def FinInductiveData : InductiveData :=
  ⟨``Fin, 1, 0, .ofList [(``Fin.mk, 0)]⟩

def FinCore : Override.Decl := ⟨``Fin, ⟦
  ,("Fin" 1 0)
⟧⟩

def Fin.mk : Override.Decl := ⟨``Fin.mk, ⟦
  (lambda (n val isLt) val)
⟧⟩

def FinMkCases (discr : Expr) (alts : Array Override.Alt) : Except String Expr := do
  let #[.alt 0 params k] := alts |
    throw "FinMkCases assumes structures having only one alternative, and never produce `default` match, got\n {alts}"
  let #[n, isLt] := params |
    throw s!"`Fin.mk` case expects exactly 2 params, got\n {params}"
  let n := n.toString false
  let isLt := isLt.toString false
  return .mkLet [(n, discr), (isLt, .atom .t)] k

protected def Fin : Override := Override.ind
  ⟨FinInductiveData, FinCore, #[Fin.mk], FinMkCases⟩

def Fin.val : Override := Override.decl ⟨``Fin.val, ⟦
  (lambda (n self) self)
⟧⟩

def Fin.valid : Override := Override.decl ⟨``Fin.isLt, ⟦
  (lambda (n self) t)
⟧⟩

def Fin.ofNat : Override := Override.decl ⟨``Fin.ofNat, ⟦
  (lambda (n val) (Fin.mk (+ n 1) (Nat.mod val (+ n 1)) t))
⟧⟩

def Fin.module := [
  Lurk.Overrides.Fin,
  Fin.val,
  Fin.valid,
  Fin.ofNat
]

end Overrides

end Lurk