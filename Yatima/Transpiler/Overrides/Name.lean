import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides

def NameInductiveData : InductiveData :=
  ⟨``Name, 0, 0, .ofList [(``Name.anonymous, 0), (``Name.str, 1), (``Name.num, 1)]⟩

def NameCore : Override.Decl := ⟨``Name, ⟦
  ,("Name" 0 0)
⟧⟩

def Name.anonymous : Override.Decl := ⟨``Name.anonymous, ⟦
  ("panic!")
⟧⟩

def Name.str : Override.Decl := ⟨``Name.str, ⟦
  ("panic!")
⟧⟩

def Name.num : Override.Decl := ⟨``Name.num, ⟦
  ("panic!")
⟧⟩

def NameMkCases (discr : AST) (alts : Array Override.Alt) : Except String AST := do
  let mut defaultElse : AST := .nil
  let mut ifThens : Array (AST × AST) := #[]
  for alt in alts do match alt with
    | .default k => defaultElse := k
    | .alt cidx params k =>
      let params : List (AST × AST) := params.toList.enum.map fun (i, param) =>
        (toAST param, ⟦(getelem _lurk_args $(i + 1))⟧)
      let case := ⟦(let $params $k)⟧
      ifThens := ifThens.push (⟦(= _lurk_idx $cidx)⟧, case)
  let cases := mkIfElses ifThens.toList defaultElse
  return ⟦(let ((_lurk_idx (getelem $discr 1))
                (_lurk_args (drop 2 $discr)))
            $cases)⟧

protected def Name : Override := Override.ind
  ⟨NameInductiveData, NameCore, #[Name.anonymous, Name.str, Name.num], NameMkCases⟩

def Name.module := [
  Lurk.Overrides.Name
]

end Overrides

end Lurk