import Yatima.CodeGen.CodeGen
import Yatima.Typechecker.Typechecker -- forcing oleans generation

def tcCode : String :=
"import Yatima.Typechecker.Typechecker
def tc := Yatima.Typechecker.typecheckConstNoStore"

open Lurk Expr.DSL DSL

def genTypechecker : IO $ Except String Expr := do
  Lean.setLibsPaths
  return Yatima.CodeGen.codeGen (← Lean.runFrontend tcCode default) `tc

/-- (= (tc decl) 1) ; tc being an expression -/
def mkRawTypecheckingExpr (tc : Expr) (decl : Digest) : Expr :=
  Expr.op₂ .numEq
    (.app tc (.atom $ .commit decl))
    (.atom $ .num $ .ofNat 1)

/-- (= (tc decl) 1) ; tc being a commitment -/
def mkCommTypecheckingExpr (tc decl : Digest) : Expr :=
  Expr.op₂ .numEq
    (.app (.atom $ .commit tc)
          (.atom $ .commit decl))
    (.atom $ .num $ .ofNat 1)
