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

  -- Load input environment
  let env ← match p.flag? "input" |>.map (·.value) with
    | none => pure default
    | some envFileName => match ← loadData envFileName false with
      | none => return 1
      | some env => pure env

  -- Run Lean frontend
  let mut cronos ← Cronos.new.clock "Run Lean frontend"
  Lean.setLibsPaths
  let path := ⟨source⟩
  let leanEnv ← Lean.runFrontend (← IO.FS.readFile path) path
  let (constMap, delta) := leanEnv.getConstsAndDelta
  cronos ← cronos.clock! "Run Lean frontend"

  let envFileName   := p.flag? "output" |>.map (·.value) |>.getD defaultEnv

  -- Start content-addressing
  cronos ← cronos.clock "Content-address"
  let stt ← match ← contAddr constMap delta env false true with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure stt
  cronos ← cronos.clock! "Content-address"

  -- dump the env
  dumpData stt.env ⟨envFileName⟩  

  return 0

def contAddrCmd : Cli.Cmd := `[Cli|
  ca VIA contAddrRun;
  "Content-addresses Lean 4 code to Yatima IR"

  FLAGS:
    i, "input"  : String;   "Optional input environment file used as cache"
    o, "output" : String; s!"Output environment file. Defaults to '{defaultEnv}'"

  ARGS:
    source : String; "Lean source file"
]
