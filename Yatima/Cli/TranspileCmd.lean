import Yatima.Cli.Utils
import Yatima.Typechecker.Typechecker
import Yatima.Transpiler.Transpiler
import Lurk.Eval

open System Yatima.Compiler Yatima.Typechecker Yatima.Transpiler in
def transpileRun (p : Cli.Parsed) : IO UInt32 := do
  let fileName := p.getArg! "input"
  match ← readStoreFromFile fileName with
  | .error err => IO.eprintln err; return 1
  | .ok store =>
    let noEraseTypes := p.hasFlag "no-erase-types" -- TODO
    let declaration : Lean.Name := .mkSimple $ p.getFlagD "declaration" "root"
    match transpile store declaration with
    | .error msg => IO.eprintln msg; return 1
    | .ok exp =>
      IO.FS.writeFile (p.getFlagD "output" "output.lurk")
        ((exp.pprint false).pretty 70)
      if p.hasFlag "run" then
        IO.println $ ← Lurk.ppEval exp
      return 0

def transpileCmd : Cli.Cmd := `[Cli|
  transpile VIA transpileRun;
  "Transpiles a Yatima IR store (from a file) to Lurk code"
  
  FLAGS:
    d, "declaration" : String; "Sets the root call for the Lurk evaluation (defaults to \"root\")"
    o, "output" : String;      "Specifies the target file name for the Lurk code (defaults to \"output.lurk\")"
    r, "run";                  "Evaluates the resulting Lurk expression with the custom evaluator"
    "no-erase-types";          "Do not erase types from the Yatima source"

  ARGS:
    input : String; "Input DagCbor binary file"
]
