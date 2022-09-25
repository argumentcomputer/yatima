import Cli
import Yatima.Cli.Utils
import Yatima.Ipld.ToIpld

def dagPut (p : Cli.Parsed) : IO UInt32 := do
  let mut cronos ← Cronos.new.clock "IPFS"
  match ← cliCompile p with
  | .ok (compileState, cronos') =>
    cronos ← cronos.clock "IPFS"
    if p.hasFlag "summary" then
      IO.println s!"{compileState.summary}"
      IO.println s!"\n{cronos'.summary}"
    let ipld := Yatima.ToIpld.storeToIpld
      compileState.constsIpld
      compileState.univAnonIpld
      compileState.exprAnonIpld
      compileState.constAnonIpld
      compileState.univMetaIpld
      compileState.exprMetaIpld
      compileState.constMetaIpld
    -- TODO: Store on IPFS using HTTP.lean
  | .error err => IO.eprintln err; return 1
  return 0

def putCmd : Cli.Cmd := `[Cli|
  put VIA dagPut;
  "Store a Yatima data store on IPFS"

  --FLAGS:
    
  ARGS:
    ...sources : String; "File name of Yatima store"
]
