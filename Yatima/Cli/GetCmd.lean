import Cli
import Yatima.Cli.Utils
import Yatima.Ipld.FromIpld
import Ipld.DagCbor

def buildGetCurlCommand (cid fileName : String) : String :=
  "curl -X POST http://127.0.0.1:5001/api/v0/dag/get?arg=" ++
  cid ++
  "&output-codec=dag-cbor --output " ++
  fileName

open System in
def getRun (p : Cli.Parsed) : IO UInt32 := do
  let cid : String := p.positionalArg! "cid" |>.as! String
  let fileName := p.getD "output" "output.bin"
  match ← runCmd (buildGetCurlCommand cid fileName) with
  | .error err => IO.eprintln err; return 1
  | .ok _ => match ← readStoreFromFile fileName with
    | .error err => IO.eprintln err; return 1
    | .ok _ => IO.println "Store retrieval succeeded"; return 0

def getCmd : Cli.Cmd := `[Cli|
  get VIA getRun;
  "Retrieve a Yatima data store from IPFS"

  FLAGS:
    o, "output" : String; "The name of the output binary file." ++
      " Defaults to \"output.bin\""
    
  ARGS:
    cid : String; "CID of stored Yatima data"
]
