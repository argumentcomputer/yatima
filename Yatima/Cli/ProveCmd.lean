import Yatima.Cli.Utils

open Cli.Parsed in
def proveRun (p : Cli.Parsed) : IO UInt32 := do
  let input : String := p.positionalArg! "input" |>.as! String
  let output := p.getD "output" "output.json"
  let proveCmd := s!"fcomm prove --expression {input} --proof {output} --lurk"
  match ← runCmd proveCmd with
  | .ok res => IO.println res; return 0
  | .error err => IO.eprintln err; return 1

def proveCmd : Cli.Cmd := `[Cli|
  prove VIA proveRun;
  "Generate a Lurk proof from a Lean declaration"

  FLAGS:
    o, "output" : String; "Name of the JSON output file. Defaults to \"output.json\""
    
  ARGS:
    input : String; "Input Lurk file"
]
