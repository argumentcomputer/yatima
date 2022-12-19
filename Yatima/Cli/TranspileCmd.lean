import Yatima.Cli.Utils
import Yatima.Transpiler.Transpiler
import Lurk.Frontend.ToExpr
import Lurk.Backend.Eval

open System Yatima.Transpiler in
def transpileRun (p : Cli.Parsed) : IO UInt32 := do
  let fileName := p.getArg! "input"
  let decl := String.toNameSafe <| p.getFlagD "decl" "root"
  match ← transpile fileName decl with
  | .error msg => IO.eprintln msg; return 1
  | .ok expr =>
    let output : System.FilePath := ⟨p.getFlagD "output" s!"lurk/{decl}.lurk"⟩
    match output.parent with
    | some dir => if ! (← dir.pathExists) then IO.FS.createDirAll dir
    | none => pure ()
    IO.println s!"Writing output to {output}"
    IO.FS.writeFile output (expr.toString true)
    if p.hasFlag "run" then
      match expr.eval with
      | .error err => IO.eprintln err; return 1
      | .ok val => IO.println val
    else if p.hasFlag "lurkrs" then
      let lurkrs := s!"lurkrs lurk/{decl}.lurk"
      IO.println s!"Running `{lurkrs}`"
      match ← runCmd lurkrs with
      | .ok res => IO.print res; return 0
      | .error err => IO.eprint err; return 1
    return 0

def transpileCmd : Cli.Cmd := `[Cli|
  transpile VIA transpileRun;
  "Transpiles a Yatima IR store (from a file) to Lurk code"

  FLAGS:
    d, "decl"   : String; "Sets the topmost call for the Lurk evaluation (defaults to \"root\")"
    o, "output" : String; "Specifies the target file name for the Lurk code (defaults to \"output.lurk\")"
    r, "run";             "Evaluates the resulting Lurk expression with a custom evaluator"
    rs, "lurkrs";         "Evaluates the resulting Lurk expression with `lurkrs`"

  ARGS:
    input : String; "Input filename to transpile"
]