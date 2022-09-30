import Yatima.Cli.Utils

def verifyRun (p : Cli.Parsed) : IO UInt32 := do
  let arg : String := p.positionalArg! "input" |>.as! String
  match ← runCmd s!"fcomm verify --proof {arg}" with
  | .error err => IO.eprintln err; return 1
  | .ok res => IO.println res; return 0
  
def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA verifyRun;
  "Verify correctness of a Lurk proof"

  ARGS:
    input : String; "Input JSON proof"
]
