import Yatima.Cli.Utils
import Yatima.Typechecker.Typechecker
import Yatima.Transpiler.Transpiler
import Yatima.ForLurkRepo.Eval

open System Yatima.Compiler Yatima.Typechecker Yatima.Transpiler Cli.Parsed in
def pipeRun (p : Cli.Parsed) : IO UInt32 := do
  let mut cronos ← Cronos.new.clock "Compilation"
  match ← cliCompile p with
  | .error err => IO.eprintln err; return 1
  | .ok (compileState, cronos') =>
    if p.hasFlag "summary" then
      IO.println s!"{compileState.summary}"
      IO.println s!"\n{cronos'.summary}"
    
    if p.hasFlag "typecheck" then
      cronos ← cronos.clock "Typechecking"
      match typecheckConsts compileState.pStore with
      | .ok _       => cronos ← cronos.clock "Typechecking"
      | .error msg  => IO.eprintln msg; return 1
    
    let eraseTypes := p.hasFlag "no-erase-types" -- TODO
    let root : Lean.Name := .mkSimple $
      p.flag? "root" |>.map (Flag.as! · String) |>.getD "root"
    cronos ← cronos.clock "Transpilation"
    match transpile compileState root with
    | .error msg => IO.eprintln msg; return 1
    | .ok exp =>
      cronos ← cronos.clock "Transpilation"
      IO.println s!"\n{cronos.summary}"
      let path ← IO.currentDir
      let output := p.flag? "output" |>.map (Flag.as! · String) |>.getD "output"
      IO.FS.createDirAll $ path/"lurk_output"
      let fname : FilePath := path/"lurk_output"/output |>.withExtension "lurk"
      IO.FS.writeFile fname s!"{(exp.pprint false).pretty 70}"
      if p.hasFlag "run" then
        IO.println $ ← Lurk.ppEval exp

      return 0

def pipeCmd : Cli.Cmd := `[Cli|
  pipe VIA pipeRun;
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
