import Cli

def dagGet (_p : Cli.Parsed) : IO UInt32 := do
  return 0

def getCmd : Cli.Cmd := `[Cli|
  get VIA dagGet;
  "Retrieve a Yatima data store from IPFS"

  --FLAGS:
    
  ARGS:
    ...sources : String; "CID of stored Yatima data"
]
