import Lake

open Lake DSL System

package Yatima {
  supportInterpreter := true
  binName := "yatima"
}

partial def getFilePaths
  (fp : FilePath) (ext : String) (acc : List FilePath := []) :
    IO (List FilePath) := do
  if ← fp.isDir then
    let mut extra : List FilePath := []
    for dirEntry in (← fp.readDir) do
      for innerFp in ← getFilePaths dirEntry.path ext do
        extra := extra.concat innerFp
    return acc ++ extra
  else
    if (fp.extension.getD "") == ext then
      return acc.concat fp
    else
      return acc

script tests do
  IO.println "building Yatima"
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["build"]
  }
  if out.exitCode != 0 then
    IO.println out.stdout
    IO.eprintln out.stderr
    return 1
  
  IO.println "creating Test.c"
  let out ← IO.Process.output {
    cmd := "lean"
    args := #["Test.lean", "-R", ".",
      "-o", "build/lib/Test.olean",
      "-i", "build/lib/Test.ilean",
      "-c", "./build/ir/Test.c"]
    env := #[("LEAN_PATH", "build/lib")]
  }
  if out.exitCode != 0 then
    IO.println out.stdout
    IO.eprintln out.stderr
    return 1

  IO.println "building Test.o from Test.c"
  let out ← IO.Process.output {
    cmd := "leanc"
    args := #["-c", "-o", "build/ir/Test.o", "build/ir/Test.c",
      "-O3", "-DNDEBUG"]
  }
  if out.exitCode != 0 then
    IO.println out.stdout
    IO.eprintln out.stderr
    return 1

  let objFilePaths := (← getFilePaths ⟨"build/ir"⟩ "o").filter
    fun fp => fp != ⟨"build/ir/Main.o"⟩

  IO.println "linking objects to build test binary"
  let out ← IO.Process.output {
    cmd := "leanc"
    args := #["-o", "build/bin/test"]
      ++ ⟨objFilePaths.map toString⟩
      ++ #["-rdynamic"]
  }
  if out.exitCode != 0 then
    IO.println out.stdout
    IO.eprintln out.stderr
    return 1
  
  IO.println "running test suite"
  let out ← IO.Process.output {
    cmd := "build/bin/test"
  }
  IO.print out.stdout
  if out.exitCode != 0 then
    IO.println out.stdout
    IO.eprint out.stderr
    return 1
  else
    IO.println "All tests passed!"
  return 0

#exit

constant libPath : String := toString $ defaultBuildDir / defaultLibDir

#eval yatimaLibPath

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
