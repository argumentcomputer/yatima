open System (FilePath)

def runCmd (cmd : String) (args : Array String) : IO $ Except String String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  return if out.exitCode != 0 then .error out.stderr
    else .ok out.stdout
