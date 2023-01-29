import Cli.Basic
import Yatima.Cli.Utils
import Yatima.ContAddr.ContAddr
import Yatima.Commit.Commit
import Yatima.Typechecker.Typechecker

open System Yatima.ContAddr Yatima.Commit Yatima.Typechecker in
def typecheckRun (p : Cli.Parsed) : IO UInt32 := do

  -- Get Lean source file name
  let some source := p.positionalArg? "source" |>.map (·.value)
    | IO.eprintln "No source was provided"; return 1

  -- Check toolchain
  if !(← validToolchain) then return 1

  -- Run Lean frontend
  let mut cronos ← Cronos.new.clock "Run Lean frontend"
  Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend ⟨source⟩
  let (constMap, delta) := leanEnv.getConstsAndDelta
  cronos ← cronos.clock! "Run Lean frontend"

  -- Start content-addressing
  cronos ← cronos.clock "Content-address"
  let caStt ← match contAddr constMap delta default with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure stt
  cronos ← cronos.clock! "Content-address"

  -- Quick commit
  cronos ← cronos.clock "Commit"
  let store ← match ← commit caStt.env.anonHashes caStt.storeAnon true false with
  | .error e => IO.eprintln e; return 1
  | .ok (stt, _) => pure stt.tcStore
  cronos ← cronos.clock! "Commit"

  -- Typecheck
  cronos ← cronos.clock "Typecheck"
  match typecheckAll store with
  | .error err => IO.eprintln err; return 1
  | .ok _ => cronos ← cronos.clock! "Typecheck"; return 0

def typecheckCmd : Cli.Cmd := `[Cli|
  tc VIA typecheckRun;
  "Typechecks all constants in a Lean file using cheap hashes"

  ARGS:
    source : String; "Lean source file"
]
