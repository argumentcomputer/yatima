import Cli.Basic
import Yatima.Cli.Utils
import Yatima.Common.IO
import Yatima.Common.LightData
import Lurk.LightData
import Lurk.Eval

open Lurk Scalar Expr.DSL DSL in
def proveRun (p : Cli.Parsed) : IO UInt32 := do
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

  let storeFileName : System.FilePath :=
    p.flag? "store" |>.map (·.value) |>.getD ⟨s!"{decl}.ldstore"⟩

  let output := match p.flag? "lurk" |>.map (·.value) with
    | some output => ⟨output⟩
    | none => s!"{decl}.lurk"

  let mut expr := default
  let mut store := default

  if p.hasFlag "raw-tc" then
    expr ← match ← genTypechecker with
      | .error msg => IO.eprintln msg; return 1
      | .ok expr' => pure expr'

    -- simply apply the typechecker to the constant hash
    expr := .app expr ⟦$declComm⟧

    -- setting up the store
    store ← match stt.extractComms env.hashes with
      | .error err => IO.eprintln err; return 1
      | .ok store' => pure store'
  else
    let some (tcComm : F) ← loadData TCHASH false | return 1

    -- call `eval` on the typechecker committed as LDON
    expr := ⟦((eval (open $tcComm)) $declComm)⟧

    -- setting up the store
    store ← match stt.extractComms (env.hashes.push tcComm) with
      | .error err => IO.eprintln err; return 1
      | .ok store' => pure store'

  -- Write the store
  dumpData store storeFileName
  
  -- Write Lurk file
  IO.FS.writeFile output s!"{expr.toFormat true}"

  -- Run if requested
  if p.hasFlag "run" then
    match expr.evaluate store with
    | .ok (v, n) =>
      IO.println s!"[{n} evaluations] => {v}"
    | .error (err, frames) =>
      IO.eprintln err
      let nFrames := (p.flag? "frames").map (·.as! Nat) |>.getD 5
      let framesFilePath := output.withExtension "frames"
      IO.FS.writeFile framesFilePath (frames.pprint nFrames)
      IO.eprintln s!"Dumped {nFrames} frames to {framesFilePath}"
      return 1
  else if p.hasFlag "lurkrs" then
    match ← runCmd "lurkrs" #[output.toString] with
    | .ok res => IO.print res; return 0
    | .error err => IO.eprint err; return 1

  return 0

def proveCmd : Cli.Cmd := `[Cli|
  prove VIA proveRun;
  "Generates Lurk source file with the typechecking code for a committed declaration"

  FLAGS:
    e, "env"   : String; "Input environment file"
    l, "lurk"  : String; "Specifies the target file name for the Lurk code (defaults to '<decl>.lurk')"
    s, "store" : String; "Output store file (defaults to '<decl>.ldstore')"
    "raw-tc";            "Flag to generate a Lurk file with explicit typechecker code"
    r, "run";            "Evaluates the resulting Lurk expression with the custom evaluator"
    f, "frames" : Nat;   "The number of frames dumped to a file in case of an error with the custom evaluator (defaults to 5)"
    rs, "lurkrs";        "Evaluates the resulting Lurk expression with `lurkrs`"

  ARGS:
    decl : String; "Declaration to be typechecked"
]
