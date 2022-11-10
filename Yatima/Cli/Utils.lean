import Yatima.Compiler.Compiler
-- import Yatima.Transpiler.Transpiler
import Yatima.Cli.Cronos
import Lurk.SerDe.Deserialize
import Lurk.Hashing.Decoding
import Yatima.Lurk.FromLurkData
import Cli

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

open System in
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

def List.pop : (l : List α) → l ≠ [] → α × Array α
  | a :: as, _ => (a, ⟨as⟩)

def runCmd (cmd : String) (cwd : Option System.FilePath := none) : IO (Except String String) := do
  let cmd := cmd.splitOn " "
  if h : cmd ≠ [] then
    let (cmd, args) := cmd.pop h
    let out ← IO.Process.output {
      cmd := cmd
      args := args
      cwd := cwd
    }
    return if out.exitCode != 0 then .error out.stderr
      else .ok out.stdout
  else return .ok ""

open Cli.Parsed

def Cli.Parsed.getFlagD (p : Cli.Parsed) (flag : String) (default : String) : String :=
  p.flag? flag |>.map (Flag.as! · String) |>.getD default

def Cli.Parsed.getArg! (p : Cli.Parsed) (arg : String) : String :=
  p.positionalArg! arg |>.as! String

open Yatima IR Lurk
def readStoreFromFile (fileName : String) : IO $ Except String IR.Store :=
  return match SerDe.deserialize (← IO.FS.readBinFile fileName) with
  | .error err => .error (toString err)
  | .ok (ptrs, store) => do
    let [ptr] := ptrs
      | throw "store deserialization error: only one root is expected"
    let data ← Hashing.decode ptr store
    match LurkData.toIRStore data with
    | some irStore => .ok irStore
    | none => throw "store deserialization error: malformed store"
