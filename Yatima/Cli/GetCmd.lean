import Cli
import Yatima.Ipld.FromIpld
import Ipld.DagCbor

def getRun (_p : Cli.Parsed) : IO UInt32 := do
  let body : String := sorry
  let bytes := body.toUTF8
  match DagCbor.deserialize bytes with
  | .ok ipld =>
    match Yatima.Ipld.storeFromIpld ipld with
    | some _ => IO.println "IPLD deserialization succeeded"
    | none => IO.println "IPLD deserialization failed"
    return 0
  | _ => IO.eprintln "DagCbor deserialization failed"; return 1

def getCmd : Cli.Cmd := `[Cli|
  get VIA getRun;
  "Retrieve a Yatima data store from IPFS"

  --FLAGS:
    
  ARGS:
    ...sources : String; "CID of stored Yatima data"
]
