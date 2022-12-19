import Yatima.Transpiler.Override

namespace Lurk

open Lean.Compiler.LCNF
open Lurk.Backend DSL
open Yatima.Transpiler

namespace Overrides

def IntInductiveData : InductiveData :=
  ⟨``Int, 0, 0, .ofList [(``Int.ofNat, 0), (``Int.negSucc, 1)]⟩

def IntCore : Override.Decl := ⟨``Int, ⟦
  ,("Int" 0 0 Fin)
⟧⟩

def Int.ofNat : Override.Decl := ⟨``Int.ofNat, ⟦
  (lambda (n) n)
⟧⟩

def Int.negSucc : Override.Decl := ⟨``Int.negSucc, ⟦
  (lambda (n) (- 0 (+ n 1)))
⟧⟩

def IntMkCases (discr : Expr) (alts : Array Override.Alt) : Except String Expr := do
  let mut defaultElse : Expr := .atom .nil
  let mut ifThens : Array (Expr × Expr) := #[]
  for alt in alts do match alt with
    | .default k => defaultElse := k
    | .alt cidx params k =>
      if cidx == 0 then
        let #[n] := params |
          throw s!"`Int.ofNat` case expects exactly 0 params, got\n {params}"
        let n := n.toString false
        let case := .let n discr k
        ifThens := ifThens.push (⟦(<= 0 $discr)⟧, case)
      else if cidx == 1 then
        let #[n] := params |
          throw s!"`Int.negSucc` case expects exactly 1 param, got\n {params}"
        let n := n.toString false
        -- n => -(n + 1) = x
        -- -x - 1 => n
        let case := .let n ⟦(- (- 0 $discr) 1)⟧ k
        ifThens := ifThens.push (⟦(< $discr 0)⟧, case)
      else
        throw s!"{cidx} is not a valid `Int` constructor index"
  let cases := Expr.mkIfElses ifThens.toList defaultElse
  return cases

protected def Int : Override := Override.ind
  ⟨IntInductiveData, IntCore, #[Int.ofNat, Int.negSucc], IntMkCases⟩


def Int.neg : Override := Override.decl ⟨``Int.neg, ⟦
  (lambda (n) (- 0 n))
⟧⟩

def Int.add : Override := Override.decl ⟨``Int.add, ⟦
  (lambda (a b) (+ a b))
⟧⟩

def Int.sub : Override := Override.decl ⟨``Int.sub, ⟦
  (lambda (a b) (- a b))
⟧⟩

def Int.mul : Override := Override.decl ⟨``Int.mul, ⟦
  (lambda (a b) (* a b))
⟧⟩

def Int.natAbs : Override := Override.decl ⟨``Int.natAbs, ⟦
  (lambda (m) (if (<= 0 m) m (- 0 m)))
⟧⟩

def Int.div : Override := Override.decl ⟨``Int.div, ⟦
  (lambda (a b)
    (let ((a (Int.natAbs a))
          (b (Int.natAbs b)))
        (if (= (<= 0 a) (<= 0 b))
            (Nat.div a b)
            (Int.neg (Nat.div a b)))))
⟧⟩

def Int.mod : Override := Override.decl ⟨``Int.mod, ⟦
  (lambda (a b)
    (let ((a (Int.natAbs a))
          (b (Int.natAbs b)))
        (if (<= 0 a)
            (Nat.mod a b)
            (Int.neg (Nat.mod a b)))))
⟧⟩

def Int.decLe : Override := Override.decl ⟨``Int.decLe, ⟦
  (lambda (a b) (to_bool (<= a b)))
⟧⟩

def Int.decLt : Override := Override.decl ⟨``Int.decLt, ⟦
  (lambda (a b) (to_bool (< a b)))
⟧⟩

def Int.decEq : Override := Override.decl ⟨``Int.decEq, ⟦
  (lambda (a b) (to_bool (= a b)))
⟧⟩

def Int.module := [
  Lurk.Overrides.Int,
  Int.neg,
  Int.add,
  Int.sub,
  Int.mul,
  Int.natAbs,
  Int.div,
  Int.mod,
  Int.decLe,
  Int.decLt,
  Int.decEq
]

end Overrides

end Lurk