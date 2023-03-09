import Cli.Basic
import Yatima.Cli.Utils
import Yatima.ContAddr.ContAddr

def defaultEnv : String :=
  "out.yenv"

def defaultStore : String :=
  "out.store"

open Yatima.ContAddr in
def contAddrRun (p : Cli.Parsed) : IO UInt32 := do

  -- Check toolchain
  if !(← validToolchain) then return 1

  -- Get Lean source file name
  let some source := p.positionalArg? "source" |>.map (·.value)
    | IO.eprintln "No source was provided"; return 1

  -- Load input environment
  let env ← match p.flag? "env" |>.map (·.value) with
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

  let envFileName   := p.flag? "output-env"   |>.map (·.value) |>.getD defaultEnv
  let storeFileName := p.flag? "output-store" |>.map (·.value) |>.getD defaultStore

  -- Start content-addressing
  cronos ← cronos.clock "Content-address"
  match ← contAddr constMap delta env false true with
  | .error err => IO.eprintln err; return 1
  | .ok stt =>
    cronos ← cronos.clock! "Content-address"

    -- dump the env
    let env : LightData := Encodable.encode stt.env
    dumpData env ⟨envFileName⟩

    -- dump the store
    let ldonHashState := stt.ldonHashState
    let store : LightData := Encodable.encode $
      ldonHashState.storeFromCommits stt.env.hashes
    dumpData store ⟨storeFileName⟩

  return 0

def contAddrCmd : Cli.Cmd := `[Cli|
  ca VIA contAddrRun;
  "Content-addresses Lean 4 code to Yatima IR"

  FLAGS:
    e,  "env"          : String;   "Optional input environment file used as cache"
    oe, "output-env"   : String; s!"Output environment file. Defaults to '{defaultEnv}'"
    os, "output-store" : String; s!"Output store file. Defaults to '{defaultStore}'"

  ARGS:
    source : String; "Lean source file"
]
