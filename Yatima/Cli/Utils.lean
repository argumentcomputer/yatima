import YatimaStdLib.Cronos
import Yatima.CodeGen.CodeGen
import Yatima.Typechecker.Typechecker -- forcing oleans generation

-- Move to YatimaStdLib
def Cronos.clock! (c : Cronos) (tag : String) : IO Cronos := do
  let now ← IO.monoNanosNow
  match c.refs.find? tag with
  | none => return { c with refs := c.refs.insert tag now }
  | some ref =>
    let time := now - ref
    IO.println s!"  {tag} | {(Float.ofNat time) / 1000000000}s"
    return {
      refs := c.refs.insert tag now,
      data := c.data.insert tag time }

open System (FilePath)

def runCmd (cmd : String) (args : Array String) : IO $ Except String String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  return if out.exitCode != 0 then .error out.stderr
    else .ok out.stdout

def validToolchain : IO Bool := do
  match ← runCmd "lake" #["--version"] with
  | .error e => IO.eprintln e; return false
  | .ok out =>
    let version := out.splitOn "(Lean version " |>.get! 1
    let version := version.splitOn ")" |>.head!
    let expectedVersion := Lean.versionString
    if version != expectedVersion then
      IO.eprintln s!"Expected toolchain '{expectedVersion}' but got '{version}'"
      return false
    return true

def tcCode : String :=
"import Yatima.Typechecker.Typechecker
def tc := Yatima.Typechecker.typecheckConstNoStore"

def genTypechecker : IO $ Except String Lurk.Expr := do
  Lean.setLibsPaths
  match Yatima.CodeGen.codeGen (← Lean.runFrontend tcCode default) "tc" with
  | .error msg => return .error msg
  | .ok   expr => return .ok expr
