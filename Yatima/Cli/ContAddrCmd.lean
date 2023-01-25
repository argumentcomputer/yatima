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
    let mut stt := default
    mkDirs
    for arg in args do
      for filePath in ← getLeanFilePaths ⟨arg⟩ do
        let env ← Lean.runFrontend filePath
        let (constMap, delta) := env.getConstsAndDelta
        match ← contAddr constMap delta stt with
        | .error err => IO.eprintln err; return 1
        | .ok stt' =>
          for (name, _) in constMap.toList do
            if stt.env.irHashes.contains name then
              IO.eprintln s!"Conflicting constants for {name}"
              return 1
          stt := stt'
    return 0

def contAddrCmd : Cli.Cmd := `[Cli|
  ca VIA contAddrRun;
  "Content-addresses Lean 4 code to Yatima IR and writes the resulting IPLD" ++
    " data encoded with DagCbor to the file system"

  FLAGS:
    o, "output" : String; "The name of the output binary file." ++
      " Defaults to \"output.ir\""
    p, "prelude"; "Optimizes the content-addressing of prelude files without" ++
      " imports. All files to be content-addressed must follow this rule"
    l, "log";     "Logs content-addressing progress"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
