import Cli
import Yatima.Cli.Utils
import Yatima.Ipld.FromIpld
import Ipld.DagCbor

def getURL : String := "http://127.0.0.1:5001/api/v0/dag/get?arg="

def stringToIpld (s : String) : Option Ipld :=
  match DagCbor.deserialize s.toUTF8 with
  | .ok ipld => some ipld
  | _ => none

open System in
def getRun (p : Cli.Parsed) : IO UInt32 := do
  let cid : String := p.positionalArg! "cid" |>.as! String
  let getCmdStr := s!"curl -X POST {getURL}" ++ cid
  IO.println s!"info: Running {getCmdStr}"
  match ← runCmd getCmdStr with
  | .error err => IO.eprintln err; return 1
  | .ok res =>
    IO.println s!"IPFS output: {res}"
    let path ← IO.currentDir
    let fname : FilePath := path/"ipfs_output" |>.withExtension "txt"
    IO.FS.writeFile fname (res ++"\n")
    IO.println s!"Wrote output to {fname}"
    match stringToIpld res with
    | none => IO.eprintln "Error deserializing string"; return 1
    | some ipld =>
      match Yatima.Ipld.storeFromIpld ipld with
      | none => IO.eprintln "Error deserializing IPLD"; return 1
      | some _ => IO.println "Store retrieval succeeded"; return 0

def getCmd : Cli.Cmd := `[Cli|
  get VIA getRun;
  "Retrieve a Yatima data store from IPFS"

  --FLAGS:
    
  ARGS:
    cid : String; "CID of stored Yatima data"
]
