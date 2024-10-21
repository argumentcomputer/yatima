import Yatima.CodeGen.CodeGen
import Yatima.Typechecker.Typechecker -- forcing oleans generation

def tcCode : String :=
"import Yatima.Typechecker.Typechecker
def tc := Yatima.Typechecker.typecheckConstNoStore"

open Lurk Expr.DSL DSL

def genTypechecker : IO $ Except String Expr := do
  Lean.setLibsPaths
  return Yatima.CodeGen.codeGen (← Lean.runFrontend tcCode default) `tc

def mkRawTypecheckingExpr (tc : Expr) (decl : F) : Expr :=
  ⟦(= $(Expr.app tc ⟦$decl⟧) 1)⟧

def mkCommTypecheckingExpr (tc decl : F) : Expr :=
  ⟦(= ((eval (open $tc)) $decl) 1)⟧
