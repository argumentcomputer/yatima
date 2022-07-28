import Cli
import Yatima.Cli.Utils
import Yatima.Cli.Cronos
import Yatima.Cli.Version
import Yatima.Compiler.Compiler
import Yatima.Typechecker.Typechecker

open Yatima.Typechecker in
open Yatima.Compiler in
def compileRun (p : Cli.Parsed) : IO UInt32 := do
  match ← getToolchain with
  | .error msg => IO.eprintln msg; return 1
  | .ok toolchain =>
    if toolchain != Lean.versionString then
      IO.eprintln
        s!"Expected toolchain '{Lean.versionString}' but got '{toolchain}'"
      return 1
  let log := p.hasFlag "log"
  match p.variableArgsAs? String with
  | some ⟨args⟩ =>
    if !args.isEmpty then
      if !(p.hasFlag "prelude") then setLibsPaths
      let mut stt : CompileState := default
      let mut errMsg : Option String := none
      let mut cronos := Cronos.new
      for arg in args do
        for filePath in ← getLeanFilePathsList ⟨arg⟩ do
          let filePathStr := filePath.toString
          cronos ← cronos.clock filePathStr
          match ← compile filePath log stt with
          | .ok stt' => match stt.union stt' with
            | .ok stt' =>
              stt := stt'
              cronos ← cronos.clock filePathStr
            | .error msg => errMsg := some msg; break
          | .error msg => errMsg := some (toString msg); break
        if errMsg.isSome then break
      match errMsg with
      | some msg =>
        IO.eprintln msg
        return 1
      | none => pure ()
      if p.hasFlag "summary" then
        IO.println s!"{stt.summary}"
        IO.println s!"\n{cronos.summary}"
      -- TODO: write `stt.store` on disk
      discard $ Yatima.Typechecker.typecheck stt.store
      return 0
    else
      IO.eprintln "No store argument was found."
      IO.eprintln "Run `yatima store -h` for further information."
      return 1
  | none =>
    IO.eprintln "Couldn't parse store arguments."
    IO.eprintln "Run `yatima store -h` for further information."
    return 1

instance : Coe String (Option String) where coe := some

def compileCmd : Cli.Cmd := `[Cli|
  compile VIA compileRun; [VERSION]
  "Compile Lean 4 code to content-addressed IPLD"

  FLAGS:
    p, "prelude"; "Optimizes the compilation of prelude files without imports." ++
      " All files to be compiled must follow this rule"
    l, "log";     "Logs compilation progress"
    s, "summary"; "Prints a compilation summary at the end of the process"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
