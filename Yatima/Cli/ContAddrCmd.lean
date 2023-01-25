import Cli.Basic
import Yatima.ContAddr.ContAddr

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

open System (FilePath)

partial def getLeanFilePaths (fp : FilePath) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    (← fp.readDir).foldlM (fun acc dir => getLeanFilePaths dir.path acc) acc
  else return if fp.extension == some "lean" then acc.push fp else acc

def Cli.Parsed.getStringFlag? (p : Cli.Parsed) (flag : String) : Option String :=
  p.flag? flag |>.map (Flag.as! · String)

def Cli.Parsed.getStringFlagD (p : Cli.Parsed) (flag : String) (default : String) : String :=
  p.getStringFlag? flag |>.getD default

def defaultEnv : String :=
  "env.yenv"

open Yatima.ContAddr in
def contAddrRun (p : Cli.Parsed) : IO UInt32 := do
  match ← getToolchain with
  | .error msg => IO.eprintln msg; return 1
  | .ok toolchain =>
    if toolchain != Lean.versionString then
      IO.eprintln s!"Expected toolchain '{Lean.versionString}' but got '{toolchain}'"
      return 1
  match p.variableArgsAs? String with
  | none =>
    IO.eprintln $ "Couldn't parse arguments.\nRun `yatima ca -h` for further information."
    return 1
  | some ⟨args⟩ =>
    if args.isEmpty then
      IO.eprintln $ "No argument was found.\nRun `yatima ca -h` for further information."
      return 1
    if !(p.hasFlag "prelude") then Lean.setLibsPaths
    mkDirs
    let mut envIn := default
    match p.getStringFlag? "in" with
    | some fileName =>
      match LightData.ofByteArray (← IO.FS.readBinFile ⟨fileName⟩) with
      | .error e =>
        IO.eprintln s!"Error deserializing input environment: {e}"
        return 1
      | .ok data =>
        have h : Encodable Yatima.IR.Env LightData String := inferInstance
        match h.decode data with
        | .ok env => envIn := env
        | .error e =>
          IO.eprintln s!"Error decoding input environment: {e}"
          return 1
    | none => pure ()
    let mut stt := envIn
    for arg in args do
      for filePath in ← getLeanFilePaths ⟨arg⟩ do
        let env ← Lean.runFrontend filePath
        let (constMap, delta) := env.getConstsAndDelta
        match ← contAddr constMap delta stt with
        | .error err => IO.eprintln err; return 1
        | .ok stt' => stt := stt'
    let envOutLD : LightData := Encodable.encode stt
    IO.FS.writeBinFile ⟨p.getStringFlagD "out" defaultEnv⟩ envOutLD.toByteArray
    return 0

def contAddrCmd : Cli.Cmd := `[Cli|
  ca VIA contAddrRun;
  "Content-addresses Lean 4 code to Yatima IR"

  FLAGS:
    i, "in"  : String; "Optional input environment file used as cache"
    o, "out" : String; s!"Output environment file. Defaults to '{defaultEnv}'"
    p, "prelude"; "Doesn't set the paths to olean files (faster for preludes)"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
