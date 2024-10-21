import Lake

open Lake DSL

package Yatima

@[default_target]
lean_exe yatima where
  supportInterpreter := true
  root := `Main

lean_lib Yatima { roots := #[`Yatima] }

require LSpec from git
  "https://github.com/argumentcomputer/LSpec.git" @ "v4.12.0"

require YatimaStdLib from git
  "https://github.com/argumentcomputer/YatimaStdLib.lean" @ "v4.12.0"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "main"

require Lurk from git
  "https://github.com/argumentcomputer/Lurk.lean" @ "v4.12.0"

require LightData from git
  "https://github.com/lurk-lab/LightData" @ "v4.12.0"

require batteries from git
  "https://github.com/leanprover-community/batteries/" @ "v4.12.0"

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
