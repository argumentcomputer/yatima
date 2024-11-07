import Cli.Basic
import Yatima.Cli.Utils
import Yatima.ContAddr.ContAddr
import Yatima.Common.GenTypechecker
import Lurk.LDON

open Yatima.ContAddr Lurk.LDON.Macro in
def makeRun (p : Cli.Parsed) : IO UInt32 := do
  -- Get Lean source file name
  let some source := p.positionalArg? "source" |>.map (·.value)
    | IO.eprintln "No source was provided"; return 1
  let some decl := p.flag? "decl" |>.map (·.value.toNameSafe)
    | IO.eprintln "No declaration provided"; return 1
  let out := match p.flag? "out" |>.map (·.value) with
    | some out => ⟨out⟩
    | none => ⟨s!"{decl}.lurk"⟩

  -- Run Lean frontend
  let mut cronos ← Cronos.new.clock "Run Lean frontend"
  Lean.setLibsPaths
  let path := ⟨source⟩
  let leanEnv ← Lean.runFrontend (← IO.FS.readFile path) path
  let constMap := leanEnv.constants
  cronos ← cronos.clock! "Run Lean frontend"

  -- Start content-addressing
  cronos ← cronos.clock "Content-address"
  let stt ← match ← mkConsts constMap decl with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure stt
  cronos ← cronos.clock! "Content-address"

  let commExprs := stt.commits.keysList.map fun c => ~[.sym "commit", c.toLDON]
  let commExprsStr := String.intercalate "\n" $ commExprs.map (·.toString false)

  cronos ← cronos.clock "Generate typechecker"
  let tcExpr ← match ← genTypechecker with
    | .error msg => IO.eprintln msg; return 1
    | .ok expr' => pure expr'
  cronos ← cronos.clock! "Generate typechecker"

  -- simply apply the typechecker to the constant hash
  let declComm := stt.env.consts.find! decl
  let expr := mkRawTypecheckingExpr tcExpr declComm

  IO.println s!"Writing output to {out}"
  IO.FS.writeFile out s!"{commExprsStr}\n{expr.toString}"

  return 0

def makeCmd : Cli.Cmd := `[Cli|
  mk VIA makeRun;
  "Generates Lurk code to typecheck a declaration"

  FLAGS:
    d, "decl" : String; "Declaration to typecheck"
    o, "out"  : String; "Output Lurk file (defaults to '<decl>.lurk')"

  ARGS:
    source : String; "Lean source file"
]
