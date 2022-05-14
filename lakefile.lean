import Lake

open Lake DSL System

package Yatima {
  srcDir  := "src"
  binRoot := "Yatima"
  binName := "yatima"
  supportInterpreter := true
}

constant yatimaLibPath : String := toString $ defaultBuildDir / defaultLibDir

inductive Result
  | success : String → Result
  | failure : String → Result

def runTest (testFilePath : FilePath) : IO Result := do
  let testProcessOutput ← IO.Process.output {
    cmd := "lean"
    args := #[testFilePath.toString]
    env := #[("LEAN_PATH", yatimaLibPath)]
  }
  if testProcessOutput.exitCode == 0 then
    return .success testProcessOutput.stdout
  else
    return .failure testProcessOutput.stderr

partial def getLeanFilePaths (fp : FilePath) (acc : List FilePath := []) :
    IO (List FilePath) := do
  if ← fp.isDir then
    let mut extra : List FilePath := []
    for dirEntry in (← fp.readDir) do
      for innerFp in ← getLeanFilePaths dirEntry.path do
        extra := extra.concat innerFp
    return acc ++ extra
  else
    if (fp.extension.getD "") == "lean" then
      return acc.concat fp
    else
      return acc

def inToOut (path : FilePath) : FilePath :=
  ⟨path.toString.replace "/in/" "/out/" |>.replace ".lean" ".out"⟩

script tests do
  let testIns ← getLeanFilePaths ⟨"test/in"⟩
  for testIn in testIns do
    let testOut := inToOut testIn
    if ← testOut.pathExists then
      match ← runTest testIn with
      | .success testResultContent =>
        let testExpectedContent ← IO.FS.readFile testOut
        if testExpectedContent == testResultContent then
          IO.println s!"✓ {testIn}"
        else
          IO.eprintln $ s!"Test failed for {testIn}\n" ++
            s!"· Expected:\n{testExpectedContent}\n" ++
            s!"· Result:\n{testResultContent}"
          return (1 : UInt32)
      | .failure s =>
        IO.eprintln s!"Failed to run {testIn} with the error:\n{s}"
        return 1
    else
      IO.eprintln s!"Failed to find {testOut}"
      return 1
  return 0
