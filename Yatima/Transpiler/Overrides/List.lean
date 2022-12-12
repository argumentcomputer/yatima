import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides

def ListInductiveData : InductiveData :=
  ⟨``List, 0, 0, .ofList [(``List.nil, 0), (``List.cons, 1)]⟩

def ListCore : Override.Decl := ⟨``List, ⟦
  (lambda (x) ,("List" 1 0))
⟧⟩

def List.nil : Override.Decl := ⟨``List.nil, ⟦
  (lambda (x) nil)
⟧⟩

def List.cons : Override.Decl := ⟨``List.cons, ⟦
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

protected def List : Override := Override.ind
  ⟨ListInductiveData, ListCore, #[List.nil, List.cons], ListMkCases⟩

def List.hasDecEq : Override := Override.decl ⟨``List.hasDecEq, ⟦
  () -- TODO FIXME
⟧⟩

def List.beq : Override := Override.decl ⟨``List.beq, ⟦
  () -- TODO FIXME: have to compare using `_inst`
  -- (lambda (α _inst xs ys) (
  --   if (_inst xs ys)
  --     ,(("Bool" 0 0) 1)
  --     ,(("Bool" 0 0) 0)))
⟧⟩

def List.hasDecidableLt : Override := Override.decl ⟨``List.hasDecidableLt, ⟦
  (lambda (α inst h l₁ l₂)
    (if l₁
        (if l₂
            (let ((a (car l₁))
                  (as (cdr l₁))
                  (b (car l₂))
                  (bs (cdr l₂))
                  (_lurk_idx (getelem (h a b) 1)))
                (if (= _lurk_idx 1)
                    Bool.true
                    (let ((_lurk_idx (getelem (h b a) 1)))
                        (if (= _lurk_idx 1)
                            Bool.false
                            (List.hasDecidableLt α inst h as bs)))))
            Bool.false)
        (if l₂
            Bool.true
            Bool.false)))
⟧⟩

def List.module := [
  Lurk.Overrides.List,
  List.hasDecidableLt
]

end Overrides

end Lurk