import Yatima.Cli.Utils

def verifyRun (p : Cli.Parsed) : IO UInt32 := do 
  match p.variableArgsAs? String with 
  | some ⟨[arg]⟩ => 
    let verify := s!"fcomm verify --proof {arg}"
    IO.println s!"info: Running {verify}"
    match ← runCmd verify with
    | .ok res => IO.println res; return 0
    | .error err => IO.eprintln err; return 1
  | _ => 
    IO.println "Couldn't parse arguments.\nRun `yatima verify -h` for further information."
    return 1
  
def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA verifyRun;
  "Verify correctness of a Lurk proof"

  ARGS:
    ...sources : String; "Input proof json"
]
