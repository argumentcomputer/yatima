import Lake

open Lake DSL

package Yatima

@[default_target]
lean_exe yatima where
  supportInterpreter := true
  root := `Main

lean_lib Yatima { roots := #[`Yatima] }

require LSpec from git
  "https://github.com/lurk-lab/LSpec.git" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "10f2b444390a41ede90ca5c038c6ff972014d433"

require Cli from git
  "https://github.com/lurk-lab/Cli.lean" @ "ef6f9bcd1738638fca8d319dbee653540d56614e"

require Lurk from git
  "https://github.com/yatima-inc/Lurk.lean" @ "29a622e4cf93017acc215d5e1f154b1c5f53e4b4"

require LightData from git
  "https://github.com/lurk-lab/LightData" @ "6dfd01c9e056deaf5b76e20f995c39e840bbde86"

require std from git
  "https://github.com/leanprover/std4/" @ "fde95b16907bf38ea3f310af406868fc6bcf48d1"

section Testing

lean_lib TestsUtils

lean_lib Fixtures {
  roots := #[
    `Fixtures.AnonGroups.ToBeImported,
    `Fixtures.AnonGroups.ToImport,

    `Fixtures.Termination.Init.Prelude,
    `Fixtures.Termination.Init.Coe,
    `Fixtures.Termination.Init.Notation,
    `Fixtures.Termination.Init.Tactics,
    `Fixtures.Termination.Init.SizeOf,
    `Fixtures.Termination.Init.Core]
}

lean_exe Tests.AnonGroups.Definitions      { supportInterpreter := true }
lean_exe Tests.AnonGroups.Inductives       { supportInterpreter := true }
lean_exe Tests.AnonGroups.ToImport         { supportInterpreter := true }
lean_exe Tests.Termination.NastyInductives { supportInterpreter := true }
lean_exe Tests.Termination.TrickyDef       { supportInterpreter := true }
lean_exe Tests.Termination.Init            { supportInterpreter := true }
lean_exe Tests.CodeGeneration.Primitives   { supportInterpreter := true }
lean_exe Tests.CodeGeneration.TrickyTypes  { supportInterpreter := true }
lean_exe Tests.Typechecker.Accept          { supportInterpreter := true }
lean_exe Tests.Typechecker.Reject          { supportInterpreter := true }
lean_exe Tests.Typechecker.TypecheckInLurk { supportInterpreter := true }

end Testing

section Setup

def runCmd (cmd : String) : ScriptM $ Except String String := do
  let cmd := cmd.splitOn " "
  if h : cmd ≠ [] then
    let (cmd, args) := match h' : cmd with
      | cmd :: args => (cmd, ⟨args⟩)
      | []          => absurd h' (h' ▸ h)
    let out ← IO.Process.output {
      cmd  := cmd
      args := args
    }
    return if out.exitCode != 0
      then .error out.stderr
      else .ok out.stdout
  else return .ok ""

script setup do
  IO.println "building yatima"
  match ← runCmd "lake exe yatima pin" with
  | .error e => IO.eprintln e; return 1
  | .ok _ =>
    match ← runCmd "lake build" with
    | .error e => IO.eprintln e; return 1
    | .ok _ => pure ()
    let binDir ← match ← IO.getEnv "HOME" with
      | some homeDir =>
        let binDir : FilePath := homeDir / ".local" / "bin"
        IO.print s!"target directory for the yatima binary? (default={binDir}) "
        let input := (← (← IO.getStdin).getLine).trim
        pure $ if input.isEmpty then binDir else ⟨input⟩
      | none =>
        IO.print s!"target directory for the yatima binary? "
        let binDir := (← (← IO.getStdin).getLine).trim
        if binDir.isEmpty then
          IO.eprintln "target directory can't be empty"; return 1
        pure ⟨binDir⟩
    IO.FS.writeBinFile (binDir / "yatima")
      (← IO.FS.readBinFile $ "build" / "bin" / "yatima")
    IO.println s!"yatima binary placed at {binDir}"
    IO.println "compiling and hashing the typechecker"
    match ← runCmd "lake exe yatima gentc" with
    | .error err => IO.eprintln err; return 1
    | .ok out => IO.print out; return 0

end Setup

section ImportAll

open System

partial def getLeanFilePaths (fp : FilePath) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    (← fp.readDir).foldlM (fun acc dir => getLeanFilePaths dir.path acc) acc
  else return if fp.extension == some "lean" then acc.push fp else acc

open Lean (RBTree)

def getAllFiles : ScriptM $ List String := do
  let paths := (← getLeanFilePaths ⟨"Yatima"⟩).map toString
  let paths : RBTree String compare := RBTree.ofList paths.toList -- ordering
  return paths.toList

def getImportsString : ScriptM String := do
  let paths ← getAllFiles
  let imports := paths.map fun p =>
    "import " ++ (p.splitOn ".").head!.replace "/" "."
  return s!"{"\n".intercalate imports}\n"

script import_all do
  IO.FS.writeFile ⟨"Yatima.lean"⟩ (← getImportsString)
  return 0

script import_all? do
  let importsFromUser ← IO.FS.readFile ⟨"Yatima.lean"⟩
  let expectedImports ← getImportsString
  if importsFromUser != expectedImports then
    IO.eprintln "Invalid import list in 'Yatima.lean'"
    IO.eprintln "Try running 'lake run import_all'"
    return 1
  return 0

end ImportAll
