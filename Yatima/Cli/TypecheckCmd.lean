import Cli.Basic
import Yatima.Cli.Utils
import Yatima.ContAddr.ContAddr
import Yatima.Typechecker.Typechecker

open System Yatima.ContAddr Yatima.Typechecker in
def typecheckRun (p : Cli.Parsed) : IO UInt32 := do
  -- Get Lean source file name
  let some source := p.positionalArg? "source" |>.map (·.value)
    | IO.eprintln "No source was provided"; return 1

  let mut cronos := Cronos.new

  -- Run Lean frontend
  cronos ← cronos.clock "Run Lean frontend"
  Lean.setLibsPaths
  let path := ⟨source⟩
  let leanEnv ← Lean.runFrontend (← IO.FS.readFile path) path
  let (constMap, delta) := leanEnv.getConstsAndDelta
  cronos ← cronos.clock! "Run Lean frontend"

  -- Start content-addressing
  cronos ← cronos.clock "Content-address"
  let stt ← match ← contAddr constMap delta true false with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure stt
  cronos ← cronos.clock! "Content-address"

  -- Typecheck
  cronos ← cronos.clock "Typecheck"
  match typecheckAll stt.store stt.env.constNames with
  | .error err => IO.eprintln err; return 1
  | .ok _ => _ ← cronos.clock! "Typecheck"; return 0

def typecheckCmd : Cli.Cmd := `[Cli|
  tc VIA typecheckRun;
  "Typechecks all constants in a Lean source file using cheap hashes"

  ARGS:
    source : String; "Lean source file"
]
