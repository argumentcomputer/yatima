import Yatima.Cli.Utils
import Yatima.Typechecker.Typechecker
import Yatima.Transpiler.Transpiler
import Yatima.ForLurkRepo.Eval

open System Yatima.Compiler Yatima.Typechecker in
def typecheckRun (p : Cli.Parsed) : IO UInt32 := do
  let mut cronos ← Cronos.new.clock "Compilation"
  match ← cliCompile p with
  | .error err => IO.eprintln err; return 1
  | .ok (compileState, cronos') =>
    cronos ← cronos.clock "Compilation"
    if p.hasFlag "summary" then
      IO.println s!"{compileState.summary}"
      IO.println s!"\n{cronos'.summary}"

    cronos ← cronos.clock "Typechecking"
    match typecheckConsts compileState.pStore with
    | .ok _       =>
      cronos ← cronos.clock "Typechecking"
      IO.println cronos.summary
      return 0
    | .error msg  => IO.eprintln msg; return 1

def typecheckCmd : Cli.Cmd := `[Cli|
  typecheck VIA typecheckRun;
  "Typecheck Yatima IR"
  
  FLAGS:
    p, "prelude"; "Optimizes the compilation of prelude files without imports." ++
      " All files to be compiled must follow this rule"
    l, "log";     "Logs compilation progress"
    s, "summary"; "Prints a compilation summary at the end of the process"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
