import Cli.Basic
import Yatima.Cli.Utils
import Lurk.Eval

open System Yatima.CodeGen in
def codeGenRun (p : Cli.Parsed) : IO UInt32 := do
  -- Parse Lean file and target declaration
  let some source := p.positionalArg? "source" |>.map (·.value)
    | IO.eprintln "No source was provided"; return 1
  let some decl := p.flag? "decl" |>.map (·.value.toNameSafe)
    | IO.eprintln "No declaration provided"; return 1

  -- Compute Lurk expression
  Lean.setLibsPaths
  let path := ⟨source⟩
  let expr ← match codeGen (← Lean.runFrontend (← IO.FS.readFile path) path) decl with
  | .error msg => IO.eprintln msg; return 1
  | .ok expr => pure $ if p.hasFlag "anon" then expr.anon else expr

  -- Write Lurk file
  let output := match p.flag? "lurk" |>.map (·.value) with
    | some output => ⟨output⟩
    | none => ⟨s!"{decl}.lurk"⟩

  IO.println s!"Writing output to {output}"
  IO.FS.writeFile output (expr.toString true)

  -- Run if requested
  if p.hasFlag "run" then
    match expr.evaluate with
    | .ok (val, iterations) =>
      IO.println s!"Iterations: {iterations}"
      IO.println val
    | .error (err, frames) =>
      IO.eprintln err
      let nFrames := (p.flag? "frames").map (·.as! Nat) |>.getD 5
      let framesFilePath := output.withExtension "frames"
      IO.FS.writeFile framesFilePath (frames.pprint nFrames)
      IO.eprintln s!"Dumped {nFrames} frames to {framesFilePath}"
      return 1
  else if p.hasFlag "lurkrs" then
    match ← runCmd "lurkrs" #[output.toString] with
    | .ok res => IO.print res; return 0
    | .error err => IO.eprint err; return 1

  return 0

def codeGenCmd : Cli.Cmd := `[Cli|
  gen VIA codeGenRun;
  "Generates Lurk code from Lean 4 code"

  FLAGS:
    d, "decl"   : String; "Sets the topmost call for the Lurk evaluation"
    a, "anon";            "Anonymizes variable names for a more compact code"
    o, "lurk"   : String; "Specifies the target file name for the Lurk code (defaults to '<decl>.lurk')"
    r, "run";             "Evaluates the resulting Lurk expression with the custom evaluator"
    f, "frames" : Nat;    "The number of frames dumped to a file in case of an error with the custom evaluator (defaults to 5)"
    rs, "lurkrs";         "Evaluates the resulting Lurk expression with `lurkrs`"

  ARGS:
    source : String; "Lean 4 file name to be translated to Lurk"
]
