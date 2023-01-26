import Cli.Basic
import Yatima.Cli.Utils
import Yatima.ContAddr.LightData
import Yatima.Commit.Commit

open Yatima.Commit in
def commitRun (p : Cli.Parsed) : IO UInt32 := do
  let some decls := p.variableArgsAs? String |>.map (·.map (·.toNameSafe))
    | IO.eprintln "TODO"; return 1
  let some envFileName := p.flag? "env" |>.map (·.value)
    | IO.eprintln "TODO"; return 1
  let .ok env ← loadEnv envFileName
    | IO.eprintln "TODO"; return 1
  let store := sorry
  match ← commit sorry store with
  | .error e => sorry
  | .ok comms => IO.println comms; return 0

def commitCmd : Cli.Cmd := `[Cli|
  cm VIA commitRun;
  "TODO"

  FLAGS:
    e, "env" : String; "Optional input environment file used as cache"

  ARGS:
    ...decls : String; "TODO"
]