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
