import Yatima.Cli.Utils
import Yatima.Transpiler2.Command
import Yatima.Transpiler2.Transpiler
import Lurk.Evaluation.FromAST
import Lurk.Evaluation.Eval

open System Yatima.Compiler Yatima.Typechecker Yatima.Transpiler2 in
def transpile2Run (p : Cli.Parsed) : IO UInt32 := do
  let fileName := p.getArg! "input"
  let declaration := String.toName <| p.getFlagD "declaration" "root"
  let (decls, s, env) ← Lean.Elab.compile fileName #[declaration]
  let decls := decls.foldl (init := .empty) fun acc decl => acc.insert decl.name decl
  let transpileEnv := ⟨s.lctx, decls, env.constants, .empty⟩
  match transpile transpileEnv declaration with
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
    return 0

def transpile2Cmd : Cli.Cmd := `[Cli|
  transpile2 VIA transpile2Run;
  "Transpiles a Yatima IR store (from a file) to Lurk code"
  
  FLAGS:
    d, "declaration" : String; "Sets the root call for the Lurk evaluation (defaults to \"root\")"
    o, "output" : String;      "Specifies the target file name for the Lurk code (defaults to \"output.lurk\")"
    r, "run";                  "Evaluates the resulting Lurk expression with the custom evaluator"

  ARGS:
    input : String; "Input filename to transpile"
]
