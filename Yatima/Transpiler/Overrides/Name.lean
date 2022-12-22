import Yatima.Transpiler.Override

namespace Lurk

open Lean.Compiler.LCNF
open Lurk.Backend DSL
open Yatima.Transpiler

namespace Overrides

def Lean.NameInductiveData : InductiveData :=
  ⟨``Lean.Name, 0, 0, .ofList [(``Lean.Name.anonymous, 0), (``Lean.Name.str, 1), (``Lean.Name.num, 2)]⟩

def Lean.NameCore : Override.Decl := ⟨``Lean.Name, ⟦
  ,("Lean.Name" 0 0)
⟧⟩

def Lean.Name.anonymous : Override.Decl := ⟨``Lean.Name.anonymous, ⟦
  ("panic!")
⟧⟩

def Lean.Name.str : Override.Decl := ⟨``Lean.Name.str, ⟦
  ("panic!")
⟧⟩

def Lean.Name.num : Override.Decl := ⟨``Lean.Name.num, ⟦
  ("panic!")
⟧⟩

def Lean.NameMkCases (discr : Expr) (alts : Array Override.Alt) : Except String Expr := do
  let mut defaultElse : Expr := .atom .nil
  let mut ifThens : Array (Expr × Expr) := #[]
  for alt in alts do match alt with
    | .default k => defaultElse := k
    | .alt cidx params k =>
      let params : List (String × Expr) := params.toList.enum.map fun (i, param) =>
        (param.toString false, ⟦(getelem _lurk_args $(i + 1))⟧)
      let case := .mkLet params k
      ifThens := ifThens.push (⟦(= _lurk_idx $cidx)⟧, case)
  let cases := Expr.mkIfElses ifThens.toList defaultElse
  return ⟦(let ((_lurk_idx (getelem $discr 1))
                (_lurk_args (drop 2 $discr)))
            $cases)⟧

protected def Lean.Name : Override := Override.ind
  ⟨Lean.NameInductiveData, Lean.NameCore, #[Lean.Name.anonymous, Lean.Name.str, Lean.Name.num], Lean.NameMkCases⟩

def Lean.Name.module := [
  Lurk.Overrides.Lean.Name
]

end Overrides

end Lurk