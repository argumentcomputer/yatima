import Cli
import Yatima.Cli.Utils
import Yatima.Compiler.Compiler
import Yatima.Typechecker.Typechecker

open Yatima.Typechecker in
open Yatima.Compiler in
def typecheckRun (p : Cli.Parsed) : IO UInt32 := do
  match ← getToolchain with
  | .error msg => IO.eprintln msg; return 1
  | .ok toolchain =>
    if toolchain != Lean.versionString then
      IO.eprintln
        s!"Expected toolchain '{Lean.versionString}' but got '{toolchain}'"
      return 1
  match p.variableArgsAs? String with
  | some ⟨args⟩ =>
    if !args.isEmpty then
      if !(p.hasFlag "prelude") then setLibsPaths
      let mut stt : CompileState := default
      let mut errMsg : Option String := none
      for arg in args do
        for filePath in ← getLeanFilePathsList ⟨arg⟩ do
          match ← compile filePath .false stt with
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
      let defns ← if not $ p.hasFlag "ipld" then pure stt.defns else match Yatima.FromIpld.extractConstArray stt.store with
        | .ok e => pure e
        | .error e => IO.eprintln s!"{e}"; return 1
      match Yatima.Typechecker.typecheck defns with
      | .ok _ => return 0
      | .error e => IO.eprintln s!"{e}"; return 1
    else
      IO.eprintln "No store argument was found."
      IO.eprintln "Run `yatima store -h` for further information."
      return 1
  | none =>
    IO.eprintln "Couldn't parse store arguments."
    IO.eprintln "Run `yatima store -h` for further information."
    return 1

instance : Coe String (Option String) where coe := some

def typecheckCmd : Cli.Cmd := `[Cli|
  typecheck VIA typecheckRun;
  "Typecheck Yatima IR"

  FLAGS:
    p, "prelude"; "Optimizes the compilation of prelude files without imports." ++
      " All files to be compiled must follow this rule"
    i, "ipld"; "Typecheck from the IPLD store"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
