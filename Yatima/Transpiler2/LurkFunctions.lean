import Lurk.Syntax.DSL
import Yatima.Transpiler2.Override

/-!
# Helper Functions for the Transpiler and Examples

This file provides all helper functions needed to construct Lurk functions
from Yatima expressions.

Currently, inductives encode three pieces of information.
1. The name of the inductive. This is not used anywhere in the transpiler,
    but is useful to keep around for humans to debug and identify objects.
2. The number of parameters. Used to generate projections.
3. The number of indices. Also used to generate projections.

This information is somewhat arbitrary. It's the bare minimum needed to
make things work. If there are better representations or we need more
metadata it should be freely changed.
-/

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler2

namespace Preloads2

def append : Name × AST := (`append, ⟦
  (lambda (xs ys) (
    if xs
      (cons (car xs) (append (cdr xs) ys))
      ys))
⟧)

def str_append : Name × AST := (`str_append, ⟦
  (lambda (xs ys)
    (if (eq "" xs)
      ys
      (strcons
        (car xs)
        (str_append (cdr xs) ys))))
⟧)

def length : Name × AST := (`length, ⟦
  (lambda (xs) (
    if xs
      (+ 1 (length (cdr xs)))
      0))
⟧)

def take : Name × AST := (`take, ⟦
  (lambda (n xs) (
    if (= n 0)
      nil
      (if xs
        (cons (car xs) (take (- n 1) (cdr xs)))
        xs)
    )
  )
⟧)

def drop : Name × AST := (`drop, ⟦
  (lambda (n xs)
    (if (= n 0)
      xs
      (if xs
        (drop (- n 1) (cdr xs))
        xs)))
⟧)

def getelem : Name × AST := (`getelem, ⟦
  (lambda (xs n)
    (if (= n 0)
      (car xs)
      (getelem (cdr xs) (- n 1))))
⟧)

def neq : Name × AST := (`neq, ⟦
  (lambda (x y) (if (eq x y) nil t))
⟧)

def str_mk : Name × AST := (`str_mk, ⟦
  (lambda (cs)
    (if cs
      (strcons (car cs) (str_mk (cdr cs)))
      ""
    )
  )
⟧)

def str_data : Name × AST := (`str_data, ⟦
  (lambda (s)
    (if (eq s "")
      nil
      (cons (car s) (str_data (cdr s)))
    )
  )
⟧)

end Preloads2

namespace Overrides2

/-!
It's important that all overrides match with existing Lean names, so using
double backticks here can help mitigate some error.
-/

def NatInductiveData : InductiveData :=
  ⟨``Nat, 0, 0, .ofList [(``Nat.zero, 0), (``Nat.succ, 1)]⟩

def NatCore : Override.Decl := ⟨``Nat, ⟦
  ,("Nat" 0 0 Fin)
⟧⟩

def NatZero : Override.Decl := ⟨``Nat.zero, ⟦
  0
⟧⟩

def NatSucc : Override.Decl := ⟨``Nat.succ, ⟦
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
          throw "`Nat.succ` case expects exactly 1 param, got\n {params}"
        let case : AST := ⟦(let (($param (- $discr 1))) $k)⟧
        ifThens := ifThens.push (⟦(neq $discr 0)⟧, case)
      else
        throw "{cidx} is not a valid `Nat` constructor index"
  let cases := mkIfElses ifThens.toList defaultElse
  return cases

def Nat : Override := Override.ind
  ⟨NatInductiveData, NatCore, #[NatZero, NatSucc], NatMkCases⟩

def NatAdd : Override := Override.decl ⟨``Nat.add, ⟦
  (lambda (a b) (+ a b))
⟧⟩

def NatSub : Override := Override.decl ⟨``Nat.sub, ⟦
  (lambda (a b)
    (if (< a b)
      0
      (- a b)))
⟧⟩

def NatMul : Override := Override.decl ⟨``Nat.mul, ⟦
  (lambda (a b) (* a b))
⟧⟩

def NatDiv : Override := Override.decl ⟨``Nat.div, ⟦
  (lambda (a b)
    (if (< a b)
      0
      (+ 1 (|Nat.div| (- a b) b))))
⟧⟩

def NatMod : Override := Override.decl ⟨``Nat.mod, ⟦
  (lambda (a b)
    (if (= b 0)
        a
        (if (< a b)
            a
            (- a (* (|Nat.div| a b) b)))))
⟧⟩

def NatDecLe : Override := Override.decl ⟨``Nat.decLe, ⟦
  (lambda (a b)
    (if (<= a b)
      ,(("Decidable" 1 0) 1 ("Nat.le" 1 1) t)
      ,(("Decidable" 1 0) 0 ("Nat.le" 1 1) t)))
⟧⟩

def NatDecLt : Override := Override.decl ⟨``Nat.decLt, ⟦
  (lambda (a b)
    (if (< a b)
      ,(("Decidable" 1 0) 1 ("Nat.lt" 1 1) t)
      ,(("Decidable" 1 0) 0 ("Nat.lt" 1 1) t)))
⟧⟩

def NatBeq : Override := Override.decl ⟨``Nat.beq, ⟦
  (lambda (a b) (
    if (= a b)
      ,(("Bool" 0 0) 1)
      ,(("Bool" 0 0) 0)))
⟧⟩

def ListInductiveData : InductiveData :=
  ⟨``List, 0, 0, .ofList [(``List.nil, 0), (``List.cons, 1)]⟩

def ListCore : Override.Decl := ⟨``List, ⟦
  (lambda (x) ,("List" 1 0))
⟧⟩

def ListNil : Override.Decl := ⟨``List.nil, ⟦
  (lambda (x) nil)
⟧⟩

def ListCons : Override.Decl := ⟨``List.cons, ⟦
  (lambda (x head tail) (cons head tail))
⟧⟩

def ListMkCases (discr : AST) (alts : Array Override.Alt) : Except String AST := do
  let mut defaultElse : AST := .nil
  let mut ifThens : Array (AST × AST) := #[]
  for alt in alts do match alt with
    | .default k => defaultElse := k
    | .alt cidx params k =>
      if cidx == 0 then
        unless params.isEmpty do
          throw s!"`List.nil` case expects exactly 0 params, got\n {params}"
        ifThens := ifThens.push (⟦(eq $discr nil)⟧, k)
      else if cidx == 1 then
        let #[head, tail] := params |
          throw "`List.cons` case expects exactly 2 params, got\n {params}"
        let case : AST := ⟦(let (($head (car $discr)) ($tail (cdr $discr))) $k)⟧
        ifThens := ifThens.push (⟦(neq $discr nil)⟧, case)
      else
        throw "{cidx} is not a valid `List` constructor index"
  let cases := mkIfElses ifThens.toList defaultElse
  return cases

def List : Override := Override.ind
  ⟨ListInductiveData, ListCore, #[ListNil, ListCons], ListMkCases⟩

def ListHasDecEq : Override := Override.decl ⟨``List.hasDecEq, ⟦
  (lambda (α _inst a b)
    (if (eq a b)
      ,(("Decidable" 1 0) 1 ("Nat.le" 1 1) t)
      ,(("Decidable" 1 0) 0 ("Nat.le" 1 1) t)))
⟧⟩

def ListMap : Override := Override.decl ⟨``List.map, ⟦
  (lambda (α β f xs)
    (if xs
      (cons (f (car xs)) (List.map α β f (cdr xs)))
      nil))
⟧⟩

def ListFoldl : Override := Override.decl ⟨``List.foldl, ⟦
  (lambda (α β f init xs)
    (if xs
      (List.foldl α β f (f init (car xs)) (cdr xs))
      init))
⟧⟩

def ListBeq : Override := Override.decl ⟨``List.beq, ⟦
  (lambda (α _inst xs ys) (
    if (_inst xs ys)
      ,(("Bool" 0 0) 1)
      ,(("Bool" 0 0) 0)))
⟧⟩

def FinInductiveData : InductiveData :=
  ⟨``Fin, 1, 0, .ofList [(``Fin.mk, 0)]⟩

def FinCore : Override.Decl := ⟨``Fin, ⟦
  ,("Fin" 1 0)
⟧⟩

def FinMk : Override.Decl := ⟨``Fin.mk, ⟦
  (lambda (n val isLt) val)
⟧⟩

def FinVal : Override.Decl := ⟨``Fin.val, ⟦
  (lambda (n self) self)
⟧⟩

def FinValid : Override.Decl := ⟨``Fin.isLt, ⟦
  (lambda (n self) t)
⟧⟩

def FinMkCases (discr : AST) (alts : Array Override.Alt) : Except String AST := do
  let #[.alt 0 params k] := alts |
    throw "we assume that structures only have one alternative, and never produce `default` match cases"
  let #[n, isLt] := params |
    throw s!"`Fin.mk` case expects exactly 2 params, got\n {params}"
  return ⟦(let (($n $discr) ($isLt t)) $k)⟧

def Fin : Override := Override.ind
  ⟨FinInductiveData, FinCore, #[FinMk], FinMkCases⟩

def FinOfNat : Override := Override.decl ⟨``Fin.ofNat, ⟦
  (lambda (n val) (Fin.mk (+ n 1) (Nat.mod val (+ n 1)) t))
⟧⟩

def CharInductiveData : InductiveData :=
  ⟨``Char, 0, 0, .ofList [(``Char.mk, 0)]⟩

def CharCore : Override.Decl := ⟨``Char, ⟦
  ,("Char" 0 0)
⟧⟩

def CharMk : Override.Decl := ⟨``Char.mk, ⟦
  (lambda (val valid)
    (char (getelem (getelem val 2) 3)))
⟧⟩

def CharVal : Override.Decl := ⟨``Char.val, ⟦
  (lambda (self)
    (UInt32.mk (Fin.mk UInt32.size (num self) t)))
⟧⟩

def CharValid : Override.Decl := ⟨``Char.valid, ⟦
  (lambda (self) t)
⟧⟩

def CharMkCases (discr : AST) (alts : Array Override.Alt) : Except String AST := do
  let mut defaultElse : AST := .nil
  let mut ifThens : Array (AST × AST) := #[]
  for alt in alts do match alt with
    | .default k => defaultElse := k
    | .alt cidx params k =>
      if cidx == 0 then
        unless params.size == 2 do
          throw s!"`Char.mk` case expects exactly 2 params, got\n {params}"
        ifThens := ifThens.push (⟦(eq $discr nil)⟧, k)
      else
        throw s!"{cidx} is not a valid `Char` constructor index"
  let cases := mkIfElses ifThens.toList defaultElse
  return cases

def Char : Override := Override.ind
  ⟨CharInductiveData, CharCore, #[CharMk], CharMkCases⟩

def CharOfNat : Override := .decl ⟨``Char.ofNat, ⟦
  (lambda (n) (char n))
⟧⟩

def StringInductiveData : InductiveData :=
  ⟨``String, 0, 0, .ofList [(``String.mk, 1)]⟩

def StringCore : Override.Decl := ⟨``String, ⟦
  ,("String" 0 0)
⟧⟩

def StringMk : Override.Decl := ⟨``String.mk, ⟦
  (lambda (data) (str_mk data))
⟧⟩

def StringData : Override.Decl := ⟨``String.data, ⟦
  (lambda (self) (str_data self))
⟧⟩

def StringMkCases (discr : AST) (alts : Array Override.Alt) : Except String AST := do
  let #[.alt 0 params k] := alts |
    throw "we assume that structures only have one alternative, and never produce `default` match cases"
  let #[data] := params |
    throw s!"`String.mk` case expects exactly 1 param, got\n {params}"
  return ⟦(let (($data (str_data $discr))) $k)⟧

def String : Override := Override.ind
  ⟨StringInductiveData, StringCore, #[StringMk], StringMkCases⟩

def StringLength : Override := Override.decl ⟨``String.length, ⟦
  (lambda (s)
    (if (eq s "")
        0
        (+ 1 (String.length (cdr s)))))
⟧⟩

def StringAppend : Override := Override.decl ⟨``String.append, ⟦
  (lambda (s₁ s₂) (str_append s₁ s₂))
⟧⟩

def String.hash : Override := Override.decl ⟨``String.hash, ⟦
  (lambda (s) (num (commit s))) -- TODO this is hackish, but if it works hey it works
⟧⟩

def mixHash : Override := Override.decl ⟨``mixHash, ⟦
  (lambda (x y) (num (commit ,(x . y)))) -- TODO this is hackish, but if it works hey it works
⟧⟩


-- def StringDecEq : Override := Override.decl ⟨``String.decEq, ⟦
--   (lambda (s₁ s₂)
--     (if (eq s₁ s₂)
--       ,(("Decidable" 1 0) 1 ("Nat.le" 1 1) t)
--       ,(("Decidable" 1 0) 0 ("Nat.le" 1 1) t)))
-- ⟧⟩

end Lurk.Overrides2
