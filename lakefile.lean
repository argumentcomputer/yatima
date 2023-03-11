import Lake

open Lake DSL

package Yatima

@[default_target]
lean_exe yatima where
  supportInterpreter := true
  root := `Main

lean_lib Yatima { roots := #[`Yatima] }

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "10f2b444390a41ede90ca5c038c6ff972014d433"

require Cli from git
  "https://github.com/yatima-inc/Cli.lean" @ "ef6f9bcd1738638fca8d319dbee653540d56614e"

require Lurk from git
  "https://github.com/yatima-inc/Lurk.lean" @ "08f710e8958261a1730ace37b973706788f5a857"

require LightData from git
  "https://github.com/yatima-inc/LightData" @ "273e5b64bdb2398592cc2aaa21bf20e576be8f0a"

require std from git
  "https://github.com/leanprover/std4/" @ "fde95b16907bf38ea3f310af406868fc6bcf48d1"

def ffiC := "ffi.c"
def ffiO := "ffi.o"

target importTarget (pkg : Package) : FilePath := do
  let oFile := pkg.oleanDir / ffiO
  let srcJob ← inputFile $ pkg.dir / ffiC
  buildFileAfterDep oFile srcJob fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    compileO ffiC oFile srcFile flags

extern_lib ffi (pkg : Package) := do
  let name := nameToStaticLib "ffi"
  let job ← fetch <| pkg.target ``importTarget
  buildStaticLib (pkg.buildDir / defaultLibDir / name) #[job]

extern_lib rust_ffi (pkg : Package) := do
  proc { cmd := "cargo", args := #["build", "--release"], cwd := pkg.dir }
  let name := nameToStaticLib "rust_ffi"
  let srcPath := pkg.dir / "target" / "release" / name
  IO.FS.createDirAll pkg.libDir
  let tgtPath := pkg.libDir / name
  IO.FS.writeBinFile tgtPath (← IO.FS.readBinFile srcPath)
  return (pure tgtPath)

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
  | .error res => IO.eprintln res; return 1
  | .ok _ =>
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
    match ← runCmd "lake exe yatima gentc" with
    | .error err => IO.eprintln err; return 1
    | .ok _ => IO.println "Lurk typechecker template stored"; return 0

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
