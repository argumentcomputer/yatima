import Cli
import Yatima.Cli.CompileCmd 
import Yatima.Transpiler.Transpiler
import Lean.Util.Path

open System Yatima.Compiler Yatima.Transpiler Cli.Parsed in
def pipeRun (p : Cli.Parsed) : IO UInt32 := do
  match ← getToolchain with
  | .error msg => IO.eprintln msg; return 1
  | .ok toolchain =>
    if toolchain != Lean.versionString then
      IO.eprintln
        s!"Expected toolchain '{Lean.versionString}' but got '{toolchain}'"
      return 1
  let log := p.hasFlag "log"
  let eraseTypes := p.hasFlag "no-erase-types"
  match p.variableArgsAs? String with
  | some ⟨args⟩ =>
    if !args.isEmpty then
      setLibsPaths
      let mut stt : CompileState := default
      let mut errMsg : Option String := none
      for arg in args do
        for filePath in ← getLeanFilePathsList ⟨arg⟩ do
          let filePathStr := filePath.toString
          match ← compile filePath log stt with
          | .ok stt' => match stt.union stt' with
            | .ok stt' =>
              stt := stt'
            | .error msg => errMsg := some msg; break
          | .error msg => errMsg := some (toString msg); break
        if errMsg.isSome then break
      match errMsg with
      | some msg =>
        IO.eprintln msg
        return 1
      | none => pure ()
      match ← transpile stt with
      | .error msg => IO.eprintln msg
      | .ok out => 
        let path ← IO.currentDir
        let output := p.flag? "output" |>.map (Flag.as! · String) |>.getD "output"
        let fname : FilePath := path/output |>.withExtension "lurk"
        IO.FS.writeFile fname s!"{out}" 
        if p.hasFlag "summary" then
          IO.println s!"{stt.summary}"
          IO.println s!"\n{out}"
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
  "Transpile Yatima IR to Lurk code"
  
  FLAGS:
    l, "log";                 "Logs transpilation progress"
    s, "summary";             "Prints a transpilation summary at the end of the process"
    o, "output" : String;     "Write resulting lurk to given output file"
    "no-erase-types";         "Do not erase types from the Yatima source"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
