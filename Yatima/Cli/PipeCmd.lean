import Yatima.Cli.CompileCmd
import Yatima.Typechecker.Typechecker
import Yatima.Transpiler.Transpiler
import Yatima.ForLurkRepo.Eval

open System Yatima.Compiler Yatima.Typechecker Yatima.Transpiler Cli.Parsed
 
def IOTranspile (stt : CompileState) (root : Lean.Name) (output : String) (run : Bool) : 
    IO Lurk.Expr := do 
  match transpile stt root with
    | .error msg => throw $ .otherError 0 msg
    | .ok exp =>
      let cronos ← Cronos.new.clock "Transpilation"
      IO.println s!"\n{cronos.summary}"
      let path ← IO.currentDir
      IO.FS.createDirAll $ path/"lurk_output"
      let fname : FilePath := path/"lurk_output"/output |>.withExtension "lurk"
      IO.FS.writeFile fname s!"{(exp.pprint false).pretty 120}"
      if run then
        IO.println $ ← Lurk.ppEval exp
      return exp

def pipeRun (p : Cli.Parsed) : IO UInt32 := do
  checkToolChain
  let eraseTypes := p.hasFlag "no-erase-types"

  match p.variableArgsAs? String with
  | some ⟨args⟩ =>
    if !args.isEmpty then
      if !(p.hasFlag "prelude") then setLibsPaths
      let log := p.hasFlag "log"
      let summary := p.hasFlag "summary"
      let stt ← IOCompile log summary args
      if p.hasFlag "typecheck" then
        let mut cronos ← Cronos.new.clock "Typechecking"
        match typecheckConsts stt.pStore with
        | .ok _       => cronos ← cronos.clock "Typechecking"
        | .error msg  => IO.eprintln msg; return 1
        IO.println cronos.summary
        
      let output := p.flag? "output" |>.map (Flag.as! · String) |>.getD "output"
      let root : Lean.Name := .mkSimple $
        p.flag? "root" |>.map (Flag.as! · String) |>.getD "root"
      let run := p.hasFlag "run"
      let exp ← IOTranspile stt root output run
      return 0
    else
      IO.eprintln "No store argument was found."
      IO.eprintln "Run `yatima pipe -h` for further information."
      return 1
  | none =>
    IO.eprintln "Couldn't parse store arguments."
    IO.eprintln "Run `yatima pipe -h` for further information."
    return 1

-- TODO: `no-erase-types` 
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
