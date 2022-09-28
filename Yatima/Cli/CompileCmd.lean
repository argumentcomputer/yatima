import Cli
import Yatima.Cli.Utils
import Yatima.Cli.Cronos
import Yatima.Compiler.Compiler

open Yatima Compiler
def IOCompile (log summary : Bool) (args : List String) : IO CompileState := do
  let mut stt : CompileState := default
  let mut cronos := Cronos.new
  for arg in args do
    for filePath in ← getLeanFilePathsList ⟨arg⟩ do
      let filePathStr := filePath.toString
      cronos ← cronos.clock filePathStr
      match ← Compiler.compile filePath log stt with
      | .ok stt' =>
        stt := stt'
        cronos ← cronos.clock filePathStr
      | .error msg => throw $ .otherError 0 (toString msg)
  if summary then
    IO.println s!"{stt.summary}"
    IO.println s!"\n{cronos.summary}"
  -- TODO: write `stt.store` on disk
  return stt

def compileRun (p : Cli.Parsed) : IO UInt32 := do
  checkToolChain
  match p.variableArgsAs? String with
  | some ⟨args⟩ =>
    if !args.isEmpty then
      if !(p.hasFlag "prelude") then setLibsPaths
      let log := p.hasFlag "log"
      let summary := p.hasFlag "summary"
      let stt ← IOCompile log summary args
      return 0
    else
      IO.eprintln "No store argument was found."
      IO.eprintln "Run `yatima store -h` for further information."
      return 1
  | none =>
    IO.eprintln "Couldn't parse store arguments."
    IO.eprintln "Run `yatima store -h` for further information."
    return 1

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
