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

open System Yatima.CodeGen Lurk.Scalar in
def genTypecheckerRun (p : Cli.Parsed) : IO UInt32 := do
  Lean.setLibsPaths
  let expr := ← match codeGen (← Lean.runFrontend tcCode default) "tc" with
    | .ok expr => return expr
    | .error msg => throw $ .userError msg

  -- generate the hash
  if p.hasFlag "hash" then
    let (hash, stt) := expr.anon.toLDON.commit default
    IO.FS.createDirAll STOREDIR
    dumpData stt LDONHASHCACHE
    dumpData hash TCHASH
    IO.println s!"Typechecker hash: {hash.asHex}"

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
  let store ← match stt.extractComms env.hashes with
    | .error err => IO.eprintln err; return 1
    | .ok store => pure store

  let tc : Lurk.Expr := .app expr $ .atom (.num declComm)

  IO.println ">> BEGIN EVAL"
  match tc.evaluate store with
  | .ok (val, iterations) =>
    IO.println s!"Iterations: {iterations}"
    IO.println val
  | .error (err, frames) =>
    let nFrames := 10
    let framesFilePath := (decl.toString : FilePath).withExtension "frames"
    IO.FS.writeFile framesFilePath (frames.pprint nFrames)
    IO.eprintln s!"Dumped {nFrames} frames to {framesFilePath}"
    IO.eprintln err
    return 1
  return 0

def genTypecheckerCmd : Cli.Cmd := `[Cli|
  gentc VIA genTypecheckerRun;
  "Stores template Lurk sources for the typechecker"

  FLAGS:
    e, "env"   : String; "Input environment file"
    l, "lurk"  : String; "Specifies the target file name for the Lurk code (defaults to '<decl>.lurk')"
    s, "store" : String; "Output store file (defaults to '<decl>.ldstore')"
    h, "hash";           "hashes the typechecker into the store"

  ARGS:
    decl : String; "Declaration to be typechecked"
]
