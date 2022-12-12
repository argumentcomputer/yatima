import Yatima.Cli.Utils
import Yatima.Transpiler.Transpiler
import Lurk.Evaluation.FromAST
import Lurk.Evaluation.Eval

open System Yatima.Transpiler in
def transpile2Run (p : Cli.Parsed) : IO UInt32 := do
  let fileName := p.getArg! "input"
  let declaration := String.toNameSafe <| p.getFlagD "declaration" "root"
  match ← transpile fileName declaration with
  | .error msg => IO.eprintln msg; return 1
  | .ok expr =>
    let output : System.FilePath := ⟨p.getFlagD "output" s!"lurk/{declaration}.lurk"⟩
    match output.parent with
    | some dir => if ! (← dir.pathExists) then IO.FS.createDirAll dir
    | none => pure ()
    IO.FS.writeFile output (expr.toString true)
    if p.hasFlag "run" then
      match expr.eval with
      | .error err => IO.eprintln err; return 1
      | .ok val => IO.println val
    else if p.hasFlag "lurkrs" then
      let lurkrs := s!"lurkrs lurk/{declaration}.lurk"
      match ← runCmd lurkrs with
      | .ok res => IO.println res; return 0
      | .error err => IO.eprintln err; return 1
    return 0

def transpileCmd : Cli.Cmd := `[Cli|
  transpile VIA transpile2Run;
  "Transpiles a Yatima IR store (from a file) to Lurk code"
  
  FLAGS:
    d, "declaration" : String; "Sets the root call for the Lurk evaluation (defaults to \"root\")"
    o, "output" : String;      "Specifies the target file name for the Lurk code (defaults to \"output.lurk\")"
    r, "run";                  "Evaluates the resulting Lurk expression with the custom evaluator"
    rs, "lurkrs";              "Evaluates the resulting Lurk expression with `lurkrs`"

  ARGS:
    input : String; "Input filename to transpile"
]