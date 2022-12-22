import Yatima.Cli.Utils
import Yatima.Ipld.ToIpld
import Yatima.ContAddr.ContAddr
import Yatima.Cli.Cronos

open System Yatima.ContAddr in
def contAddrRun (p : Cli.Parsed) : IO UInt32 := do
  match ← getToolchain with
  | .error msg => IO.eprintln msg; return 1
  | .ok toolchain =>
    if toolchain != Lean.versionString then
      IO.eprintln s!"Expected toolchain '{Lean.versionString}' but got '{toolchain}'"
  match p.variableArgsAs? String with
  | some ⟨args⟩ =>
    if !args.isEmpty then
      if !(p.hasFlag "prelude") then Lean.setLibsPaths
      let mut stt := default
      let log := p.hasFlag "log"
      let mut cronos := Cronos.new
      for arg in args do
        for filePath in ← getLeanFilePathsList ⟨arg⟩ do
          let filePathStr := filePath.toString
          cronos ← cronos.clock filePathStr
          match ← contAddr filePath log stt with
          | .ok stt' =>
            -- making sure that constants with the same name are the very same
            for (name, (cid', _)) in stt'.cache.toList do
              match stt.cache.find? name with
              | some (cid, _) =>
                if cid != cid' then
                  IO.eprintln s!"Conflicting constants for {name}"
                  return 1
              | none => pure ()
            cronos ← cronos.clock filePathStr
            stt := stt'
          | .error err => IO.eprintln err; return 1
      if p.hasFlag "summary" then
        IO.println s!"{stt.summary}"
        IO.println s!"\n{cronos.summary}"
      let ipld := Yatima.Ipld.storeToIpld stt.ipldStore
      IO.FS.writeBinFile (p.getStringFlagD "output" "output.ir") (DagCbor.serialize ipld)
      return 0
    else
      IO.eprintln $ "No store argument was found.\n" ++
        "Run `yatima store -h` for further information."
      return 1
  | none =>
    IO.eprintln $ "Couldn't parse store arguments.\n" ++
      "Run `yatima store -h` for further information."
    return 1

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
    s, "summary"; "Prints a summary at the end of the process"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]
