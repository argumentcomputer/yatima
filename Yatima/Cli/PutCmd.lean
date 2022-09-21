import Cli

def dagPut (_p : Cli.Parsed) : IO UInt32 := do
  return 0

def putCmd : Cli.Cmd := `[Cli|
  put VIA dagPut;
  "Store a Yatima data store on IPFS"

  --FLAGS:
    
  ARGS:
    ...sources : String; "File name of Yatima store"
]
