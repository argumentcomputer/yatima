import Cli.Basic
import Yatima.Cli.Utils
import Yatima.Common.Store
import Yatima.Commit.Commit

open Yatima.IR Yatima.Commit in
def commitRun (p : Cli.Parsed) : IO UInt32 := do

  -- Get declarations
  let some decls := p.variableArgsAs? String |>.map (·.map (·.toNameSafe))
    | IO.eprintln "Couldn't parse declarations"; return 1
  if decls.isEmpty then IO.eprintln "At least one declaration needed"; return 1

  -- Load environment
  let some envFileName := p.flag? "env" |>.map (·.value)
    | IO.eprintln "Environment file not provided"; return 1
  let some (env : Yatima.IR.Env) ← loadData envFileName false | return 1

  -- Get neeeded hashes
  let mut hashes := #[]
  for decl in decls do
    match env.consts.find? decl with
    | some (_, hash) => hashes := hashes.push hash
    | none => IO.eprintln s!"{decl} not found in the environment"; return 1

  let store ← match ← Yatima.IR.StoreAnon.load hashes with
    | .ok store => pure store
    | .error e => IO.println e; return 1

  -- Do slow commit
  mkCMDirs
  let start ← IO.monoMsNow
  let commits ← match ← commit hashes store false with
  | .error e => IO.eprintln e; return 1
  | .ok comms => pure comms
  let finish ← IO.monoMsNow
  let duration : Float := (finish.toFloat - start.toFloat) / 1000.0
  IO.println s!"Committing finished in {duration}s"

  decls.zip commits |>.forM IO.println
  return 0

def commitCmd : Cli.Cmd := `[Cli|
  cm VIA commitRun;
  "Computes and caches Poseidon hashes for declarations in an environment"

  FLAGS:
    e, "env" : String; "Input environment file"

  ARGS:
    ...decls : String; "Declarations to be committed"
]
