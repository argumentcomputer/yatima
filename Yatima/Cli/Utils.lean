import Yatima.Compiler.Compiler
import Yatima.Transpiler.Transpiler
import Yatima.Cli.Cronos
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

open Yatima.Compiler

def cliCompile (p : Cli.Parsed) : IO $ Except String (CompileState × Cronos) := do
  match ← getToolchain with
  | .error msg => return .error msg
  | .ok toolchain =>
    if toolchain != Lean.versionString then
      return .error s!"Expected toolchain '{Lean.versionString}' but got '{toolchain}'"
  match p.variableArgsAs? String with
  | some ⟨args⟩ =>
    if !args.isEmpty then
      if !(p.hasFlag "prelude") then setLibsPaths
      let mut stt : CompileState := default
      let log := p.hasFlag "log"
      let mut cronos := Cronos.new
      for arg in args do
        for filePath in ← getLeanFilePathsList ⟨arg⟩ do
          let filePathStr := filePath.toString
          cronos ← cronos.clock filePathStr
          match ← compile filePath log stt with
          | .ok stt' => cronos ← cronos.clock filePathStr; stt := stt'
          | .error msg => return .error $ toString msg
      return .ok (stt, cronos)
    else
      return .error $ "No store argument was found.\n" ++
        "Run `yatima store -h` for further information."
  | none =>
    return .error $ "Couldn't parse store arguments.\n" ++
      "Run `yatima store -h` for further information."

open Cli.Parsed in
def Cli.Parsed.getD (p : Cli.Parsed) (flag : String) (default : String) : String :=
  p.flag? flag |>.map (Flag.as! · String) |>.getD default

open System Yatima.Transpiler in
def cliTranspile (compileState : CompileState) (p : Cli.Parsed) :
    IO $ Except String Lurk.Expr := do
  let noEraseTypes := p.hasFlag "no-erase-types" -- TODO
  let root : Lean.Name := .mkSimple $ p.getD "declaration" "root"
  match transpile compileState root with
  | .error msg => return .error msg
  | .ok exp =>
    let path ← IO.currentDir
    let output := p.getD "output" "output"
    let fname : FilePath := path/"lurk_output"/output |>.withExtension "lurk"
    IO.FS.createDirAll $ path/"lurk_output"
    IO.FS.writeFile fname s!"{(exp.pprint false).pretty 70}"
    return .ok exp
