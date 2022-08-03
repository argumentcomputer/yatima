import Lake
import Std.Data.RBTree

open Lake DSL

package Yatima 

@[defaultTarget]
lean_exe yatima {
  supportInterpreter := true
  root := `Main
}

lean_lib Yatima { roots := #[`Yatima] }

require Ipld from git
  "https://github.com/yatima-inc/Ipld.lean" @ "c77099a6151816687750d65fea71d8cee995f29c"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "77fc51697abeff937ffd20d2050723dc0fa1c8c0"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "a2bbc9a48db7efd5d761a5b27f2cc6c1863b9622"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "112b35fc348a4a18d2111ac2c6586163330b4941"

section Testing

lean_lib TestsUtils

lean_lib Fixtures {
  roots := #[`Fixtures.AnonCidGroups.ToBeImported]
}

lean_exe Tests.AnonCidGroups.Definitions   { supportInterpreter := true }
lean_exe Tests.AnonCidGroups.Inductives    { supportInterpreter := true }
lean_exe Tests.AnonCidGroups.ToImport      { supportInterpreter := true }
lean_exe Tests.Termination.NastyInductives { supportInterpreter := true }
lean_exe Tests.Termination.Prelude         { supportInterpreter := true }

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
      | []          => absurd h' h
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

open Std (RBTree)

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
