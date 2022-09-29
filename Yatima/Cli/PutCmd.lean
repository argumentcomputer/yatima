import Cli
import Yatima.Cli.Utils
import Yatima.Ipld.ToIpld
import Ipld.DagCbor

def putURL : String := "http://127.0.0.1:5001/api/v0/dag/put?" ++
  "store-codec=dag-cbor&input-codec=dag-cbor&hash=sha3-256&allow-big-block=true"

def ipldToString (ipld : Ipld) : String :=
  String.fromUTF8Unchecked (DagCbor.serialize ipld)

open System in
def putRun (p : Cli.Parsed) : IO UInt32 := do
  let mut cronos ← Cronos.new.clock "IPFS"
  match ← cliCompile p with
  | .error err => IO.eprintln err; return 1
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
    let body := ipldToString ipld
    let path ← IO.currentDir
    let fname : FilePath := path/"myfile" |>.withExtension "json"
    IO.FS.writeBinFile fname (DagCbor.serialize ipld)
    let putCmdStr := s!"curl -X POST -H 'Content-Type: multipart/form-data' -F file=@{fname} {putURL}"
    IO.println s!"info: Running {putCmdStr}"
    match ← runCmd putCmdStr with
    | .ok res => IO.println res; return 0
    | .error err => IO.eprintln err; return 1
    
def putCmd : Cli.Cmd := `[Cli|
  put VIA putRun;
  "Store a Yatima data store on IPFS"

  FLAGS:
    p, "prelude"; "Optimizes the compilation of prelude files without imports." ++
      " All files to be compiled must follow this rule"
    l, "log";     "Logs compilation progress"
    s, "summary"; "Prints a compilation summary at the end of the process"

  ARGS:
    ...sources : String; "File name of Yatima store"
]
