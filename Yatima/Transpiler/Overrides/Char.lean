import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides2

def CharInductiveData : InductiveData :=
  ⟨``Char, 0, 0, .ofList [(``Char.mk, 0)]⟩

def CharCore : Override.Decl := ⟨``Char, ⟦
  ,("Char" 0 0)
⟧⟩

def Char.mk : Override.Decl := ⟨``Char.mk, ⟦
  (lambda (val valid)
    (char (getelem (getelem val 2) 3)))
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

protected def Char : Override := Override.ind
  ⟨CharInductiveData, CharCore, #[Char.mk], CharMkCases⟩

def Char.val : Override := Override.decl ⟨``Char.val, ⟦
  (lambda (self)
    (UInt32.mk (Fin.mk UInt32.size (num self) t)))
⟧⟩

def Char.valid : Override := Override.decl ⟨``Char.valid, ⟦
  (lambda (self) t)
⟧⟩

/-- 
Convert a `Nat` into a `Char`. 
If the `Nat` does not encode a valid unicode scalar value, `'\0'` is returned instead. 
-/
def Char.ofNat : Override := .decl ⟨``Char.ofNat, ⟦
  (lambda (n)
    -- TODO: We contradict ourselves and use `or` and `and` here, 
    -- because the cost of strict behavior is minimal
    (if (lor (land (<= 0 n) (< n 0xd800)) (land (< 0xdfff n) (< n 0x110000)))
        n
        0))
⟧⟩

def Char.module := [
  Lurk.Overrides2.Char,
  Char.val,
  Char.valid,
  Char.ofNat
]

end Overrides2

end Lurk