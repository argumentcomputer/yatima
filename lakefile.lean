import Lake

open Lake DSL

package Yatima

@[default_target]
lean_exe yatima where
  supportInterpreter := true
  root := `Main

lean_lib Yatima { roots := #[`Yatima] }

lean_lib Yatima2 { roots := #[`Yatima2] }

require Ipld from git
  "https://github.com/yatima-inc/Ipld.lean" @ "716e787eba461dba1c5b9bb9977147564865309d"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "649368d593f292227ab39b9fd08f6a448770dca8"

require Cli from git
  "https://github.com/yatima-inc/Cli.lean" @ "ef6f9bcd1738638fca8d319dbee653540d56614e"

require Lurk from git
  "https://github.com/yatima-inc/Lurk.lean" @ "bf753862b4f94553ac86ce99a82b93634209c84e"

require LightData from git
  "https://github.com/yatima-inc/LightData" @ "86c3ba909582366b03a778d8020044a73859a9ad"

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
-- lean_exe Tests.Typechecker.Reduction       { supportInterpreter := true }

end Testing

section Setup

inductive CmdResult
  | ok  : String → CmdResult
  | err : String → CmdResult

def runCmd (cmd : String) : ScriptM CmdResult := do
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
      then .err out.stderr
      else .ok out.stdout
  else return .ok ""

script setup do
  IO.println "building yatima"
  match ← runCmd "lake build" with
  | .ok  _   => match ← IO.getEnv "HOME" with
    | some homePath =>
      let binDir : String := s!"{homePath}/.local/bin"
      IO.print s!"target directory for the yatima binary? (default={binDir}) "
      let input := (← (← IO.getStdin).getLine).trim
      let binDir := if input.isEmpty then binDir else input
      cpBin binDir
    | none =>
      IO.print s!"target directory for the yatima binary? "
      let binDir := (← (← IO.getStdin).getLine).trim
      if binDir.isEmpty then
        IO.eprintln "target directory can't be empty"
        return 1
      cpBin binDir
  | .err res => IO.eprintln res; return 1
where
  cpBin (binDir : String) : ScriptM UInt32 := do
    match ← runCmd s!"cp build/bin/yatima {binDir}/yatima" with
    | .ok _    => IO.println s!"yatima binary placed at {binDir}/"; return 0
    | .err res => IO.eprintln res; return 1

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
