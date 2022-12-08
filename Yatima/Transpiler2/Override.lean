import Lean.Compiler.LCNF.Main
import Lurk.Syntax.ExprUtils

namespace Yatima.Transpiler2
open Lurk.Syntax AST DSL
open Lean Compiler.LCNF

structure InductiveData where
  name : Lean.Name
  params : Nat
  indices : Nat
  ctors : Lean.NameMap Nat

structure Override.Decl where
  declName : Name
  decl : AST

inductive Override.Alt where
  | alt (cidx : Nat) (params : Array Name) (code : AST)
  | default (code : AST)

structure Override.Inductive where
  indData : InductiveData
  ind : Override.Decl
  ctors : Array Override.Decl
  mkCases : (discr : AST) → (alts : Array Override.Alt) → Except String AST

inductive Override where
  | decl (decl : Override.Decl) : Override
  | ind (ind : Override.Inductive) : Override

def Override.name : Override → Name
  | .decl odecl => odecl.declName
  | .ind oind => oind.ind.declName

end Yatima.Transpiler2
