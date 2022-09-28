import Yatima.Cli.PipeCmd

open System Yatima.Compiler Yatima.Typechecker Yatima.Transpiler Cli.Parsed in
def verifyRun (p : Cli.Parsed) : IO UInt32 := do return 1

-- TODO
def verifyCmd : Cli.Cmd := `[Cli|
  pipe VIA verifyRun;
  "Transpile Lean 4 code to Lurk code"
  
  FLAGS:
    p, "prelude"; "Optimizes the compilation of prelude files without imports." ++
      " All files to be compiled must follow this rule"
    l, "log";             "Logs compilation progress"
    s, "summary";         "Prints a compilation summary at the end of the process"
    ty, "typecheck";      "Typechecks the Yatima IR code"
    rt, "root" : String;  "Sets the root call for the Lurk evaluation (defaults to `root`)"
    o, "output" : String; "Specifies the target file name for the Lurk code"
    r, "run";             "Runs the evaluation of the resulting Lurk expression"
    "no-erase-types";     "Do not erase types from the Yatima source"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
