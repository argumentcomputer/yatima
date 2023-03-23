import Yatima.CodeGen.CodeGen
import Yatima.Typechecker.Typechecker -- forcing oleans generation

def tcCode : String :=
"import Yatima.Typechecker.Typechecker
def tc := Yatima.Typechecker.typecheckConstNoStore"

def genTypechecker : IO $ Except String Lurk.Expr := do
  Lean.setLibsPaths
  return Yatima.CodeGen.codeGen (← Lean.runFrontend tcCode default) "tc"
