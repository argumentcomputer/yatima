import Cli.Basic
import Yatima.Cli.Utils
import Yatima.Common.IO
import Lurk.LightData

def genTypecheckerRun (_p : Cli.Parsed) : IO UInt32 := do
  let expr ← match ← genTypechecker with
    | .error msg => IO.eprintln msg; return 1
    | .ok expr => pure expr
  let (hash, stt) := expr.anon.toLDON.commit default
  IO.FS.createDirAll STOREDIR
  dumpData stt LDONHASHCACHE
  dumpData hash TCHASH
  IO.println s!"Typechecker hash: {hash.asHex}"
  return 0

def genTypecheckerCmd : Cli.Cmd := `[Cli|
  gentc VIA genTypecheckerRun;
  "Compile the typechecker to Lurk and hash it"
]
