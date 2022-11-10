import Yatima.Cli.Utils
import Yatima.LurkData.ToLurkData
import Lurk.SerDe.Serialize

open System Yatima Compiler in
def compileRun (p : Cli.Parsed) : IO UInt32 := do
  match ← getToolchain with
  | .error msg => IO.eprintln msg; return 1
  | .ok toolchain =>
    if toolchain != Lean.versionString then
      IO.eprintln s!"Expected toolchain '{Lean.versionString}' but got '{toolchain}'"
  match p.variableArgsAs? String with
  | some ⟨args⟩ =>
    if !args.isEmpty then
      if !(p.hasFlag "prelude") then setLibsPaths
      let mut stt : CompileState := default
      let log := p.hasFlag "log"
      let mut cronos := Cronos.new
      for arg in args do
        for filePath in ← getLeanFilePathsList ⟨arg⟩ do
          let filePathStr := filePath.toString
          cronos ← cronos.clock filePathStr
          match ← compile filePath log stt with
          | .ok stt' =>
            -- making sure that constants with the same name are the very same
            for (name, (cid', _)) in stt'.cache.toList do
              match stt.cache.find? name with
              | some (cid, _) =>
                if cid != cid' then
                  IO.eprintln s!"Conflicting constants for {name}"
                  return 1
              | none => pure ()
            cronos ← cronos.clock filePathStr
            stt := stt'
          | .error err => IO.eprintln err; return 1
      if p.hasFlag "summary" then
        IO.println s!"{stt.summary}"
        IO.println s!"\n{cronos.summary}"
      let (ptr, store) :=  stt.lurkStore.toLurk.encode
      let irPath : FilePath := "lurk"/p.getFlagD "output" "lurk_store.ir"
      IO.FS.writeBinFile irPath (Lurk.SerDe.serialize [ptr] store)
      let (ptr, store) :=  cidCacheToLurk stt.cidCache |>.encode
      let cachePath : FilePath := "lurk"/p.getFlagD "output" "precompiled.ir"
      IO.FS.writeBinFile cachePath (Lurk.SerDe.serialize [ptr] store)
      return 0
    else
      IO.eprintln $ "No store argument was found.\n" ++
        "Run `yatima store -h` for further information."
      return 1
  | none =>
    IO.eprintln $ "Couldn't parse store arguments.\n" ++
      "Run `yatima store -h` for further information."
    return 1

def compileCmd : Cli.Cmd := `[Cli|
  compile VIA compileRun;
  "Compiles Lean 4 code to Yatima IR and writes the resulting AST data" ++
    " encoded with Lurk Scalars to the file system"

  FLAGS:
    o, "output" : String; "The name of the output binary file." ++
      " Defaults to \"output.ir\""
    p, "prelude"; "Optimizes the compilation of prelude files without imports." ++
      " All files to be compiled must follow this rule"
    l, "log";     "Logs compilation progress"
    s, "summary"; "Prints a compilation summary at the end of the process"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
