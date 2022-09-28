import Yatima.Cli.PipeCmd

def List.pop : (l : List α) → l ≠ [] → α × Array α
  | a :: as, _ => (a, ⟨as⟩)        

def runCmd (cmd : String) : IO (Except String String) := do
  let cmd := cmd.splitOn " "
  if h : cmd ≠ [] then
    let (cmd, args) := cmd.pop h
    let out ← IO.Process.output {
      cmd := cmd
      args := args
    }
    return if out.exitCode != 0 then .error out.stderr
      else .ok out.stdout
  else return .ok ""

open Cli.Parsed in 
def runProve (p : Cli.Parsed) : IO UInt32 := do 
  checkToolChain
  let input : String := ← match p.flag? "file" with 
    | some input => return input.as! String
    | none => do throw $ .otherError 0 "no input file specified"
  let decl : String := ← match p.flag? "declaration" with 
    | some decl => return decl.as! String
    | none => do throw $ .otherError 0 "no declaration specified"
  let output := p.flag? "output" |>.map (Flag.as! · String) |>.getD "prove_output"
  let stt ← IOCompile false false [input]
  let exp ← IOTranspile stt decl "lean_output" false
  let prove := s!"cargo run --release -- prove --expression ../lean_output.lurk --proof {output}.json --lurk"
  match ← runCmd prove with 
  | .ok res => 
    IO.println s!"fcomm success" 
    return 0
  | .error err => 
    IO.eprintln s!"fcomm failed: {err}" 
    return 1

def proveCmd : Cli.Cmd := `[Cli|
  prove VIA runProve;
  "Generate a Lurk proof from a Lean declaration"

  FLAGS:
    f, "file" : String;            "Input file"
    d, "declaration" : String;     "Declaration to be transpiled"
    o, "output" : String;          "Output file. Default is `lean_output.lurk`"
]
