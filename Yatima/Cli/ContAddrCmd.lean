import Cli.Basic
import Yatima.Cli.Utils
import Yatima.ContAddr.ContAddr

def defaultEnv : String :=
  "out.yenv"

open Yatima.ContAddr in
def contAddrRun (p : Cli.Parsed) : IO UInt32 := do

  -- Check toolchain
  if !(← validToolchain) then return 1

  -- Get Lean source file name
  let some source := p.positionalArg? "source" |>.map (·.value)
    | IO.eprintln "No source was provided"; return 1

  -- Run Lean frontend
  let mut cronos ← Cronos.new.clock "Run Lean frontend"
  Lean.setLibsPaths
  let path := ⟨source⟩
  let leanEnv ← Lean.runFrontend (← IO.FS.readFile path) path
  let (constMap, delta) := leanEnv.getConstsAndDelta
  cronos ← cronos.clock! "Run Lean frontend"

  -- Start content-addressing
  cronos ← cronos.clock "Content-address"
  let stt ← match ← contAddr constMap delta false true with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure stt
  cronos ← cronos.clock! "Content-address"

  -- dump the env
  let envFileName := p.flag? "env" |>.map (·.value) |>.getD defaultEnv
  dumpData stt.env ⟨envFileName⟩  

  return 0

def contAddrCmd : Cli.Cmd := `[Cli|
  ca VIA contAddrRun;
  "Content-addresses Lean 4 code to Yatima IR"

  FLAGS:
    e, "env" : String; s!"Output environment file. Defaults to '{defaultEnv}'"

  ARGS:
    source : String; "Lean source file"
]
