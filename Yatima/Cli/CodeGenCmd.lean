import Yatima.Cli.Utils
import Yatima.CodeGen.CodeGen
import Lurk.Backend.Eval

open System Yatima.CodeGen in
def codeGenRun (p : Cli.Parsed) : IO UInt32 := do
  let fileName := p.getArg! "input"
  let decl := String.toNameSafe <| p.getStringFlagD "decl" "root"
  match ← codeGen fileName decl with
  | .error msg => IO.eprintln msg; return 1
  | .ok expr =>
    let output := ⟨p.getStringFlagD "output" s!"lurk/{decl}.lurk"⟩
    match output.parent with
    | some dir => if ! (← dir.pathExists) then IO.FS.createDirAll dir
    | none => pure ()
    IO.println s!"Writing output to {output}"
    IO.FS.writeFile output (expr.toString true)
    if p.hasFlag "run" then
      match expr.eval with
      | .error (err, frames) =>
        IO.eprintln err
        let nFrames := p.getNatFlagD "frames" 5
        let framesFilePath := output.withExtension "frames"
        IO.FS.writeFile framesFilePath (frames.pprint nFrames)
        IO.eprintln s!"Dumped {nFrames} frames to {framesFilePath}"
        return 1
      | .ok val => IO.println val
    else if p.hasFlag "lurkrs" then
      let lurkrsCmd := s!"lurkrs {output}"
      IO.println s!"Running `{lurkrsCmd}`"
      match ← runCmd lurkrsCmd with
      | .ok res => IO.print res; return 0
      | .error err => IO.eprint err; return 1
    return 0

def codeGenCmd : Cli.Cmd := `[Cli|
  gen VIA codeGenRun;
  "Generates Lurk code from Lean 4 code"

  FLAGS:
    d, "decl"   : String; "Sets the topmost call for the Lurk evaluation (defaults to \"root\")"
    o, "output" : String; "Specifies the target file name for the Lurk code (defaults to \"output.lurk\")"
    r, "run";             "Evaluates the resulting Lurk expression with the custom evaluator"
    f, "frames" : Nat;    "The number of frames dumped to a file in case of an error with the custom evaluator (defaults to 5)"
    rs, "lurkrs";         "Evaluates the resulting Lurk expression with `lurkrs`"

  ARGS:
    input : String; "Lean 4 file name to be translated to Lurk"
]
