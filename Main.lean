import Cli
import Yatima.Compiler.Frontend
import Yatima.Cronos

opaque VERSION : String := s!"{Lean.versionString}|0.0.1"

open System in
partial def getFilePathsList (fp : FilePath) (acc : List FilePath := []) :
    IO $ List FilePath := do
  if ← fp.isDir then
    let mut extra : List FilePath := []
    for dirEntry in ← fp.readDir do
      for innerFp in ← getFilePathsList dirEntry.path do
        extra := extra.concat innerFp
    return acc ++ extra
  else
    if (fp.extension.getD "") = "lean" then
      return acc.concat fp
    else
      return acc

def getToolchain : IO $ Except String String := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["--version"]
  }
  if out.exitCode != 0 then
    return .error "Couldn't run 'lake --version' command"
  else
    let version := out.stdout.splitOn "(Lean version " |>.get! 1
    return .ok $ version.splitOn ")" |>.head!

open Yatima.Compiler in
def storeRun (p : Cli.Parsed) : IO UInt32 := do
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
        for filePath in ← getFilePathsList ⟨arg⟩ do
          let filePathStr := filePath.toString
          cronos ← cronos.clock filePathStr
          match ← runFrontend filePath log stt with
          | .ok stt' => match stt.union stt' with
            | .ok stt' =>
              stt := stt'
              cronos ← cronos.clock filePathStr
            | .error msg => errMsg := some msg; break
          | .error msg => errMsg := some msg; break
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
      return 0
    else
      IO.eprintln "No store argument was found."
      IO.eprintln "Run `yatima store -h` for further information."
      return 1
  | none =>
    IO.eprintln "Couldn't parse store arguments."
    IO.eprintln "Run `yatima store -h` for further information."
    return 1

instance : Coe String (Option String) where
  coe := some

def storeCmd : Cli.Cmd := `[Cli|
  store VIA storeRun; [VERSION]
  "Compile Lean 4 code to content-addressed IPLD"

  FLAGS:
    p, "prelude"; "Optimizes the compilation of prelude files without imports." ++
      " All files to be compiled must follow this rule"
    l, "log";     "Logs compilation progress"
    s, "summary"; "Prints a compilation summary at the end of the process"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]

def printInit (_ : α) : IO UInt32 := do
  IO.println "Call `yatima --help` for more info"
  return 0

def yatimaCmd : Cli.Cmd := `[Cli|
  yatima VIA printInit; [VERSION]
  "A compiler and typechecker for the Yatima language"

  SUBCOMMANDS:
    storeCmd
]

def main (args : List String) : IO UInt32 :=
  yatimaCmd.validate args
