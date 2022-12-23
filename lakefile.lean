import Lake

open Lake DSL

package Yatima

@[default_target]
lean_exe yatima {
  supportInterpreter := true
  root := `Main
}

lean_lib Yatima { roots := #[`Yatima] }

require Ipld from git
  "https://github.com/yatima-inc/Ipld.lean" @ "9ccb24133e8d06a268b823abd51df50c97cdede3"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "89798a6cb76b2b29469ff752af2fd8543b3a5515"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "f905b68f529de2af44cf6ea63489b7e3cd090050"

require Cli from git
  "https://github.com/yatima-inc/Cli.lean" @ "cd523a1951a8ec1ffb276446280ac60a7c5ad333"

require Lurk from git
  "https://github.com/yatima-inc/Lurk.lean" @ "c771c8e7857e54dfdfa1331c3e59023f4d6ec7f8"

require std from git
  "https://github.com/leanprover/std4/" @ "d83e97c7843deb1cf4a6b2a2c72aaf2ece0b4ce8"

section Testing

lean_lib TestsUtils

lean_lib Fixtures {
  roots := #[
  `Fixtures.AnonCidGroups.ToBeImported,
  `Fixtures.AnonCidGroups.ToImport,

  `Fixtures.Termination.Init.Prelude,
  `Fixtures.Termination.Init.Coe,
  `Fixtures.Termination.Init.Notation,
  `Fixtures.Termination.Init.Tactics,
  `Fixtures.Termination.Init.SizeOf,
  `Fixtures.Termination.Init.Core
  ]
}

lean_exe Tests.AnonCidGroups.Definitions   { supportInterpreter := true }
lean_exe Tests.AnonCidGroups.Inductives    { supportInterpreter := true }
lean_exe Tests.AnonCidGroups.ToImport      { supportInterpreter := true }
lean_exe Tests.Termination.NastyInductives { supportInterpreter := true }
lean_exe Tests.Termination.Prelude         { supportInterpreter := true }
lean_exe Tests.Roundtrip.Tricky            { supportInterpreter := true }
lean_exe Tests.Typechecker.Reduction       { supportInterpreter := true }
lean_exe Tests.CodeGeneration.TrickyTypes  { supportInterpreter := true }
lean_exe Tests.CodeGeneration.Primitives   { supportInterpreter := true }

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
    let mut extra : Array FilePath := #[]
    for dirEntry in ← fp.readDir do
      for innerFp in ← getLeanFilePaths dirEntry.path do
        extra := extra.push innerFp
    return acc.append extra
  else match fp.extension with
    | some "lean" => return acc.push fp
    | _ => return acc

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
