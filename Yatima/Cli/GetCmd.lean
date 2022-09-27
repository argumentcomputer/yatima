import Cli
import Yatima.Ipld.FromIpld

def dagGet (_p : Cli.Parsed) : IO UInt32 := do
  let ipld : Ipld := sorry
  match Yatima.Ipld.storeFromIpld ipld with
  | some _ => IO.println "deserialization succeeded"
  | none => IO.println "deserialization failed"
  return 0

def getCmd : Cli.Cmd := `[Cli|
  get VIA dagGet;
  "Retrieve a Yatima data store from IPFS"

  --FLAGS:
    
  ARGS:
    ...sources : String; "CID of stored Yatima data"
]
