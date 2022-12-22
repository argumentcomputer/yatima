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
  "https://github.com/yatima-inc/Lurk.lean" @ "75aa04edfab54ed0e9211ae6558999f4462e9ce7"

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
lean_exe Tests.Transpilation.TrickyTypes   { supportInterpreter := true }
lean_exe Tests.Transpilation.Primitives    { supportInterpreter := true }

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

def getCurrDir : ScriptM String := do
  match ← runCmd "pwd" with
  | .ok res => return res.trim
  | .err e  => panic! e

def getHomeDir : ScriptM String :=
  return s!"{"/".intercalate $ (← getCurrDir).splitOn "/" |>.take 3}"

script setup do
  IO.println "building yatima"
  match ← runCmd "lake build" with
  | .ok  _   =>
    let mut binDir : String := s!"{← getHomeDir}/.local/bin"
    IO.print s!"target directory for the yatima binary? (default={binDir}) "
    let input := (← (← IO.getStdin).getLine).trim
    if !input.isEmpty then
      binDir := input
    match ← runCmd s!"cp build/bin/yatima {binDir}/yatima" with
    | .ok _    => IO.println s!"yatima binary placed at {binDir}/"; return 0
    | .err res => IO.eprintln res; return 1
  | .err res => IO.eprintln res; return 1

end Setup

section ImportAll

open System

partial def getLeanFilePathsList (fp : FilePath) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    let mut extra : Array FilePath := #[]
    for dirEntry in ← fp.readDir do
      for innerFp in ← getLeanFilePathsList dirEntry.path do
        extra := extra.push innerFp
    return acc.append extra
  else
    if (fp.extension.getD "") = "lean" then
      return acc.push fp
    else
      return acc

open Lean (RBTree)

def getAllFiles : ScriptM $ List String := do
  let paths := (← getLeanFilePathsList ⟨"Yatima"⟩).map toString
  let paths : RBTree String compare := RBTree.ofList (paths.data) -- ordering
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
