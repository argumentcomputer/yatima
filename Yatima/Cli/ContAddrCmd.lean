import Cli.Basic
import Yatima.Cli.Utils
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
  let some source := p.positionalArg? "source" |>.map (·.value)
    | IO.eprintln "No source was provided"; return 1

  -- Run Lean frontend
  Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend source
  let (constMap, delta) := leanEnv.getConstsAndDelta

  -- Load input environment
  let mut env := default
  match p.flag? "env" |>.map (·.value) with
  | none => pure ()
  | some envFileName => match ← loadEnv envFileName with
    | .error e => IO.eprintln e; return 1
    | .ok env' => env := env'

  -- Start content-addressing
  mkDirs
  match ← contAddr constMap delta env with
  | .error err => IO.eprintln err; return 1
  | .ok env' => env := env'

  -- Persist resulting environment
  let target := ⟨p.flag? "output" |>.map (·.value) |>.getD defaultEnv⟩
  have h : Encodable Yatima.IR.Env LightData String := inferInstance
  IO.FS.writeBinFile target (h.encode env)
  return 0

def contAddrCmd : Cli.Cmd := `[Cli|
  ca VIA contAddrRun;
  "Content-addresses Lean 4 code to Yatima IR"

  FLAGS:
    e, "env"    : String; "Optional input environment file used as cache"
    o, "output" : String; s!"Output environment file. Defaults to '{defaultEnv}'"

  ARGS:
    source : String; "Lean source file"
]
