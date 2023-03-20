import Cli.Basic
import Yatima.Lean.Utils
import Yatima.CodeGen.CodeGen
import Yatima.Common.IO
import Yatima.Common.LightData
import Yatima.Typechecker.Typechecker -- forcing oleans generation
import Lurk.LightData
import Lurk.Eval

def tcCode : String :=
"import Yatima.Typechecker.Typechecker
def tc := Yatima.Typechecker.typecheckConstNoStore"

open Yatima.CodeGen in
def genTypecheckerRun (_p : Cli.Parsed) : IO UInt32 := do
  Lean.setLibsPaths
  let expr ← match codeGen (← Lean.runFrontend tcCode default) "tc" with
    | .error msg => IO.eprintln msg; return 1
    | .ok expr => pure expr
  let (hash, stt) := expr.anon.toLDON.commit default
  IO.FS.createDirAll STOREDIR
  dumpData stt LDONHASHCACHE
  dumpData hash TCHASH
  IO.println s!"Typechecker hash: {hash.asHex}"
  return 0

def genTypecheckerCmd : Cli.Cmd := `[Cli|
  gentc VIA genTypecheckerRun;
  "Stores template Lurk sources for the typechecker"
]
