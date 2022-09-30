import Yatima.Cli.Utils
import Yatima.Typechecker.Typechecker
import Yatima.Transpiler.Transpiler
import Yatima.ForLurkRepo.Eval

open System Yatima.Compiler Yatima.Typechecker Yatima.Transpiler in
def transpileRun (p : Cli.Parsed) : IO UInt32 := do
  let mut cronos ← Cronos.new.clock "Compilation"
  match ← cliCompile p with
  | .error err => IO.eprintln err; return 1
  | .ok (compileState, cronos') =>
    cronos ← cronos.clock "Compilation"
    if p.hasFlag "summary" then
      IO.println s!"{compileState.summary}"
      IO.println s!"\n{cronos'.summary}"

    cronos ← cronos.clock "Transpilation"
    match ← cliTranspile compileState p with
    | .ok exp =>
      cronos ← cronos.clock "Transpilation"
      if p.hasFlag "run" then
        cronos ← cronos.clock "Evaluation"
        IO.println $ ← Lurk.ppEval exp
        cronos ← cronos.clock "Evaluation"
      IO.println s!"\n{cronos.summary}"
      return 0
    | .error msg =>
      IO.eprintln msg
      return 1

def transpileCmd : Cli.Cmd := `[Cli|
  transpile VIA transpileRun;
  "Transpiles Lean 4 code to Lurk code"
  
  FLAGS:
    p, "prelude"; "Optimizes the compilation of prelude files without imports." ++
      " All files to be compiled must follow this rule"
    l, "log";                  "Logs compilation progress"
    s, "summary";              "Prints a compilation summary at the end of the process"
    d, "declaration" : String; "Sets the root call for the Lurk evaluation (defaults to \"root\")"
    o, "output" : String;      "Specifies the target file name for the Lurk code"
    r, "run";                  "Runs the evaluation of the resulting Lurk expression"
    "no-erase-types";          "Do not erase types from the Yatima source"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
