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

def runCmd (descr cmd : String)
  (args : Array String := #[]) (env: Array (String × Option String) := #[]) :
    IO Bool := do
  IO.println descr
  let out ← IO.Process.output { cmd := cmd, args := args, env := env }
  if out.exitCode != 0 then
    IO.println  out.stdout
    IO.eprintln out.stderr
    return true
  return false

script tests do
  if ← runCmd "Creating test build directories" "mkdir"
    #["-p", "build/ir_test", "build/bin_test"] then return 1

  if ← runCmd "Building Yatima" "lake" #["build"] then return 1

  let mut testCases : List String := []

  for testFilePath in ← getFilePaths ⟨"Tests"⟩ "lean" do
    let testCase := testFilePath.fileStem.get!
    testCases := testCases.concat testCase
    if ← runCmd s!"Creating {testCase}.c" "lean"
      #[s!"Tests/{testCase}.lean", "-R", ".",
        "-o", s!"build/lib/{testCase}.olean",
        "-i", s!"build/lib/{testCase}.ilean",
        "-c", s!"./build/ir/{testCase}.c"]
      #[("LEAN_PATH", "build/lib")] then return 1

    if ← runCmd s!"building {testCase}.o from {testCase}.c" "leanc"
      #["-c", "-o", s!"build/ir_test/{testCase}.o", s!"build/ir/{testCase}.c",
        "-O3", "-DNDEBUG"] then return 1

    let objFilePaths := (← getFilePaths ⟨"build/ir"⟩ "o").filter
      fun fp => fp != ⟨"build/ir/Main.o"⟩

    if ← runCmd s!"linking objects to build the {testCase} binary" "leanc"
      (#["-o", s!"build/bin_test/{testCase}", s!"build/ir_test/{testCase}.o"]
        ++ ⟨objFilePaths.map toString⟩
        ++ #["-rdynamic"]) then return 1
  
  IO.println "-- Running tests --"
  
  let mut allPassed : Bool := true

  for testCase in testCases do
    IO.println s!"Running tests for {testCase}"
    let out ← IO.Process.output {
      cmd := s!"build/bin_test/{testCase}"
    }
    IO.print out.stdout
    if out.exitCode != 0 then
      IO.eprint out.stderr
      allPassed := false
  if allPassed then
    IO.println "\nAll tests passed!"
    return 0
  return 1
