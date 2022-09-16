import Cli
import Yatima.Cli.Utils
import Yatima.Cli.Cronos
import Yatima.Compiler.Compiler
import Yatima.Typechecker.Typechecker
import Yatima.Transpiler.Transpiler
import Yatima.ForLurkRepo.Eval
import Lean.Util.Path

open System Yatima.Compiler Yatima.Typechecker Yatima.Transpiler Cli.Parsed in
def pipeRun (p : Cli.Parsed) : IO UInt32 := do
  match ← getToolchain with
  | .error msg => IO.eprintln msg; return 1
  | .ok toolchain =>
    if toolchain != Lean.versionString then
      IO.eprintln
        s!"Expected toolchain '{Lean.versionString}' but got '{toolchain}'"
      return 1
  let eraseTypes := p.hasFlag "no-erase-types"
  let mut cronos := Cronos.new
  match p.variableArgsAs? String with
  | some ⟨args⟩ =>
    if !args.isEmpty then
      cronos ← cronos.clock "Compilation"
      if !(p.hasFlag "prelude") then setLibsPaths
      let mut stt : CompileState := default
      let log := p.hasFlag "log"
      let mut cronos' := Cronos.new
      for arg in args do
        for filePath in ← getLeanFilePathsList ⟨arg⟩ do
          let filePathStr := filePath.toString
          cronos' ← cronos'.clock filePathStr
          match ← compile filePath log stt with
          | .ok stt' =>
            stt := stt'
            cronos' ← cronos'.clock filePathStr
          | .error msg => IO.eprintln msg; return 1
      if p.hasFlag "summary" then
        IO.println s!"{stt.summary}"
        IO.println s!"\n{cronos'.summary}"

      cronos ← cronos.clock "Compilation"
      if p.hasFlag "typecheck" then
        cronos ← cronos.clock "Typechecking"
        match typecheckConsts stt.consts with
        | .ok _       => cronos ← cronos.clock "Typechecking"
        | .error msg  => IO.eprintln msg; return 1
      cronos ← cronos.clock "Transpilation"
      match ← transpile' ⟨stt, []⟩ ⟦(isZero 3)⟧ with
      | .error msg => IO.eprintln msg
      | .ok exp =>
        cronos ← cronos.clock "Transpilation"
        IO.println s!"\n{cronos.summary}"
        let path ← IO.currentDir
        let output := p.flag? "output" |>.map (Flag.as! · String) |>.getD "output"
        IO.FS.createDirAll $ path/"lurk_output"
        let fname : FilePath := path/"lurk_output"/output |>.withExtension "lurk"
        IO.FS.writeFile fname s!"{(exp.pprint false).pretty 70}"
        if p.hasFlag "run" then
          IO.println $ ← Lurk.ppEval exp default
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
    l, "log";             "Logs transpilation progress"
    s, "summary";         "Prints a transpilation summary at the end of the process"
    ty, "typecheck";      "Typechecks the Yatima IR code"
    o, "output" : String; "Specifies the target file name for the Lurk code"
    r, "run";             "Runs the evaluation of the resulting Lurk expression"
    "no-erase-types";     "Do not erase types from the Yatima source"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
