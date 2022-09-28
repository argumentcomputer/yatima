import Yatima.Cli.Utils

open Yatima.Compiler in
def compileRun (p : Cli.Parsed) : IO UInt32 := do
  let mut cronos ← Cronos.new.clock "Compilation"
  match ← cliCompile p with
  | .ok (compileState, cronos') =>
    cronos ← cronos.clock "Compilation"
    if p.hasFlag "summary" then
      IO.println s!"{compileState.summary}"
      IO.println s!"\n{cronos'.summary}"
    IO.println s!"\n{cronos.summary}"
    return 0
  | .error err => IO.eprintln err; return 1

def compileCmd : Cli.Cmd := `[Cli|
  compile VIA compileRun;
  "Compile Lean 4 code to content-addressed IPLD"

  FLAGS:
    p, "prelude"; "Optimizes the compilation of prelude files without imports." ++
      " All files to be compiled must follow this rule"
    l, "log";     "Logs compilation progress"
    s, "summary"; "Prints a compilation summary at the end of the process"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
