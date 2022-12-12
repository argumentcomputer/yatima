import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides

def NatInductiveData : InductiveData :=
  ⟨``Nat, 0, 0, .ofList [(``Nat.zero, 0), (``Nat.succ, 1)]⟩

def NatCore : Override.Decl := ⟨``Nat, ⟦
  ,("Nat" 0 0 Fin)
⟧⟩

def Nat.zero : Override.Decl := ⟨``Nat.zero, ⟦
  0
⟧⟩

def Nat.succ : Override.Decl := ⟨``Nat.succ, ⟦
  (lambda (n) (+ n 1))
⟧⟩

def NatMkCases (discr : AST) (alts : Array Override.Alt) : Except String AST := do
  let mut defaultElse : AST := .nil
  let mut ifThens : Array (AST × AST) := #[]
  for alt in alts do match alt with
    | .default k => defaultElse := k
    | .alt cidx params k =>
      if cidx == 0 then
        unless params.isEmpty do
          throw s!"`Nat.zero` case expects exactly 0 params, got\n {params}"
        ifThens := ifThens.push (⟦(= $discr 0)⟧, k)
      else if cidx == 1 then
        let #[param] := params |
          throw s!"`Nat.succ` case expects exactly 1 param, got\n {params}"
        let case : AST := ⟦(let (($param (- $discr 1))) $k)⟧
        ifThens := ifThens.push (⟦(neq $discr 0)⟧, case)
      else
        throw "{cidx} is not a valid `Nat` constructor index"
  let cases := mkIfElses ifThens.toList defaultElse
  return cases

protected def Nat : Override := Override.ind
  ⟨NatInductiveData, NatCore, #[Nat.zero, Nat.succ], NatMkCases⟩

def Nat.add : Override := Override.decl ⟨``Nat.add, ⟦
  (lambda (a b) (+ a b))
⟧⟩

def Nat.sub : Override := Override.decl ⟨``Nat.sub, ⟦
  (lambda (a b)
    (if (< a b)
      0
      (- a b)))
⟧⟩

def Nat.ml : Override := Override.decl ⟨``Nat.mul, ⟦
  (lambda (a b) (* a b))
⟧⟩

def Nat.div : Override := Override.decl ⟨``Nat.div, ⟦
  (lambda (a b)
    (if (< a b)
      0
      (+ 1 (|Nat.div| (- a b) b))))
⟧⟩

def Nat.mod : Override := Override.decl ⟨``Nat.mod, ⟦
  (lambda (a b)
    (if (= b 0)
        a
        (if (< a b)
            a
            (- a (* (|Nat.div| a b) b)))))
⟧⟩

def Nat.decLe : Override := Override.decl ⟨``Nat.decLe, ⟦
  (lambda (a b) (to_bool (<= a b)))
⟧⟩

def Nat.decLt : Override := Override.decl ⟨``Nat.decLt, ⟦
  (lambda (a b) (to_bool (< a b)))
⟧⟩

def Nat.decEq : Override := Override.decl ⟨``Nat.decEq, ⟦
  (lambda (a b) (to_bool (= a b)))
⟧⟩

def Nat.beq : Override := Override.decl ⟨``Nat.beq, ⟦
  (lambda (a b) (to_bool (= a b)))
⟧⟩

def Nat.module := [
  Lurk.Overrides.Nat,
  Nat.add,
  Nat.sub,
  Nat.ml,
  Nat.div,
  Nat.mod,
  Nat.decLe,
  Nat.decLt,
  Nat.decEq,
  Nat.beq
]

end Overrides

end Lurk