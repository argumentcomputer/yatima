import Yatima.Cli.Utils
import Yatima.Typechecker.Typechecker

open System Yatima.Typechecker in
def typecheckRun (p : Cli.Parsed) : IO UInt32 := do
  let fileName := p.getArg! "input"
  match ← readStoreFromFile fileName with
  | .error err => IO.eprintln err; return 1
  | .ok store => match typecheck store with
    | .ok _ => IO.println "Typechecking succeeded"; return 0
    | .error msg => IO.eprintln msg; return 1

def typecheckCmd : Cli.Cmd := `[Cli|
  tc VIA typecheckRun;
  "Typechecks a Yatima IR store written in a binary file"

  ARGS:
    input : String; "Input DagCbor binary file"
]
