import Cli
import Yatima.Cli.Utils
import Yatima.Ipld.ToIpld
import Ipld.DagCbor

def buildPutCurlCommand (fileName : String) : String :=
  "curl -X POST -H 'Content-Type: multipart/form-data' -F file=@" ++
  fileName ++
  " http://localhost:5001/api/v0/dag/put?" ++
  "store-codec=dag-cbor&input-codec=dag-cbor&hash=sha3-256&allow-big-block=true"

def extractCid (s : String) : String :=
  let split := s.splitOn "{\"Cid\":{\"/\":\""
  split[1]!.splitOn "\"}}" |>.head!

def putRun (p : Cli.Parsed) : IO UInt32 := do
  let fileName := p.getArg! "input"
  match ← runCmd (buildPutCurlCommand fileName) with
  | .error err => IO.eprintln err; return 1
  | .ok res => IO.println (extractCid res); return 0

def putCmd : Cli.Cmd := `[Cli|
  put VIA putRun;
  "Uses `curl` to send a Yatima IR store from a file to IPFS"

  ARGS:
    input : String; "Input DagCbor binary file"
]
