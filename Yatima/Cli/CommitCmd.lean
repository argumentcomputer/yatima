import Cli.Basic
import Yatima.Cli.Utils
import Yatima.Commit.Commit

open Yatima.Commit

def commitRun (p : Cli.Parsed) : IO UInt32 := do
  let some decls := p.variableArgsAs? String |>.map (·.map (·.toNameSafe))
    | IO.eprintln "TODO"; return 1
  let some envFileName := p.flag? "env" |>.map (·.value)
    | IO.eprintln "TODO"; return 1
  let mut env := default
  match ← loadEnv envFileName with
  | .error e => IO.eprintln e; return 1
  | .ok env' => env := env'
  let mut hashes := #[]
  for decl in decls do
    match env.consts.find? decl with
    | some (_, hash) => hashes := hashes.push hash
    | none => IO.eprintln s!"{decl} not found in the environment"; return 1
  match ← commit hashes with
  | .error e => IO.eprintln e; return 1
  | .ok comms => IO.println comms; return 0

def commitCmd : Cli.Cmd := `[Cli|
  cm VIA commitRun;
  "TODO"

  FLAGS:
    e, "env" : String; "Optional input environment file used as cache"

  ARGS:
    ...decls : String; "TODO"
]
