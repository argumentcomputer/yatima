import Cli.Basic
import Yatima.Lean.Utils
import Yatima.CodeGen.CodeGen
import Yatima.Typechecker.Typechecker -- forcing oleans generation

def tcCode : String :=
"import Yatima.Typechecker.Typechecker
def tc := Yatima.Typechecker.typecheckConstNoStore (.ofNat 0)"

open Yatima.CodeGen in
def genTypecheckerRun (_p : Cli.Parsed) : IO UInt32 := do
  Lean.setLibsPaths
  let expr ← match codeGen (← Lean.runFrontend tcCode default) "tc" with
  | .error msg => IO.eprintln msg; return 1
  | .ok expr => pure expr
  IO.FS.createDirAll STOREDIR
  IO.FS.writeFile LURKTCPATH (expr.toString true)
  return 0

def genTypecheckerCmd : Cli.Cmd := `[Cli|
  gentc VIA genTypecheckerRun;
  "Stores template Lurk sources for the typechecker"
]
