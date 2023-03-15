import Cli.Basic
import Yatima.Common.IO
import Yatima.Common.LightData

def defaultStore : String :=
  "out.ldstore"

open Lurk in
def proveRun (p : Cli.Parsed) : IO UInt32 := do

  let some (tcComm : F) ← loadData TCHASH false | return 1
  let some (stt : LDONHashState) ← loadData LDONHASHCACHE false | return 1

  -- Get environment file name
  let some decl := p.positionalArg? "decl" |>.map (·.value.toNameSafe)
    | IO.eprintln "No declaration was provided"; return 1

  -- Load environment
  let some envFileName := p.flag? "env" |>.map (·.value)
    | IO.eprintln "Environment file not provided"; return 1
  let some (env : Yatima.IR.Env) ← loadData envFileName false | return 1

  let some declComm := env.consts.find? decl
    | IO.eprintln s!"{decl} not found in the environment"; return 1

  -- setting up the store
  let store ← match stt.extractComms #[declComm, tcComm] with
    | .error err => IO.eprintln err; return 1
    | .ok store => pure store
  let storeFileName := p.flag? "store" |>.map (·.value) |>.getD defaultStore

  -- Write the store
  dumpData store storeFileName

  -- Write Lurk file
  let output := match p.flag? "lurk" |>.map (·.value) with
    | some output => ⟨output⟩
    | none => s!"{decl}.lurk"
  IO.FS.writeFile output s!"((eval (open {tcComm.asHex}))\n  {declComm.asHex})"

  return 0

def proveCmd : Cli.Cmd := `[Cli|
  prove VIA proveRun;
  "Generates Lurk source file with the typechecking code for a committed declaration"

  FLAGS:
    e, "env"   : String; "Input environment file"
    l, "lurk"  : String; "Specifies the target file name for the Lurk code (defaults to '<decl>.lurk')"
    s, "store" : String; s!"Output store file. Defaults to '{defaultStore}'"

  ARGS:
    decl : String; "Declaration to be typechecked"
]
