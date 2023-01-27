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

def defaultEnv : String :=
  "env.yenv"

open Yatima.ContAddr in
def contAddrRun (p : Cli.Parsed) : IO UInt32 := do

  -- Check toolchain
  match ← getToolchain with
  | .error msg => IO.eprintln msg; return 1
  | .ok toolchain =>
    if toolchain != Lean.versionString then
      IO.eprintln s!"Expected toolchain '{Lean.versionString}' but got '{toolchain}'"
      return 1

  -- Get Lean source file name
  let some source := p.positionalArg? "source" |>.map (·.value)
    | IO.eprintln "No source was provided"; return 1

  -- Load input environment
  let env ← match p.flag? "env" |>.map (·.value) with
  | none => pure default
  | some envFileName => match ← loadData envFileName false with
    | none => return 1
    | some env => pure env

  -- Run Lean frontend
  Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend source
  let (constMap, delta) := leanEnv.getConstsAndDelta

  -- Start content-addressing
  mkDirs
  let start ← IO.monoMsNow
  let stt ← match contAddr constMap delta env with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure stt
  let finish ← IO.monoMsNow
  let duration : Float := (finish.toFloat - start.toFloat) / 1000.0
  IO.println s!"Content-addressing finished in {duration}s"

  -- Persist resulting state
  let target := ⟨p.flag? "output" |>.map (·.value) |>.getD defaultEnv⟩
  stt.dump target
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
