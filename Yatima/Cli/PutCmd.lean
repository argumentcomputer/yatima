import Cli
import Yatima.Cli.Utils
import Yatima.Ipld.ToIpld
import Ipld.DagCbor

def buildPutCurlCommand (fileName : String) : String :=
  "curl -X POST -H 'Content-Type: multipart/form-data' -F file=@" ++
  fileName ++
  " http://localhost:5001/api/v0/dag/put?" ++
  "store-codec=dag-cbor&input-codec=dag-cbor&hash=sha3-256&allow-big-block=true"

def putRun (p : Cli.Parsed) : IO UInt32 := do
    let fileName : String := p.positionalArg! "input" |>.as! String
    match ← runCmd (buildPutCurlCommand fileName) with
    | .ok res => IO.println res; return 0
    | .error err => IO.eprintln err; return 1
    
def putCmd : Cli.Cmd := `[Cli|
  put VIA putRun;
  "Store a Yatima data store on IPFS"

  ARGS:
    input : String; "Input DagCbor binary file"
]
