import Cli.Basic
import Yatima.Common.IO
import Yatima.Common.LightData

def proveRun (p : Cli.Parsed) : IO UInt32 := do

  let tc ← do
    let path := if p.hasFlag "anon" then LURKTCANONPATH else LURKTCPATH
    if ← path.pathExists then IO.FS.readFile path
    else IO.eprintln "Typecheck template not found"; return 1

  -- Get environment file name
  let some decl := p.positionalArg? "decl" |>.map (·.value.toNameSafe)
    | IO.eprintln "No declaration was provided"; return 1

  -- Load environment
  let some envFileName := p.flag? "env" |>.map (·.value)
    | IO.eprintln "Environment file not provided"; return 1

  let some (env : Yatima.IR.Env) ← loadData envFileName false | return 1
  let some comm := env.consts.find? decl
    | IO.eprintln s!"{decl} not found in the environment"; return 1

  -- Write Lurk file
  let output := match p.flag? "output" |>.map (·.value) with
    | some output => ⟨output⟩
    | none => "lurk_tc" / s!"{decl}.lurk"
  match output.parent with
  | some dir => if ! (← dir.pathExists) then IO.FS.createDirAll dir
  | none => pure ()
  IO.println s!"Writing output to {output}"
  IO.FS.writeFile output s!"(\n{tc}\n  {comm.val})"

  return 0

def proveCmd : Cli.Cmd := `[Cli|
  prove VIA proveRun;
  "Generates Lurk source file with the typechecking code for a committed declaration"

  FLAGS:
    e, "env" : String;    "Input environment file"
    a, "anon";            "Anonymizes variable names for a more compact code"
    o, "output" : String; "Specifies the target file name for the Lurk code (defaults to 'lurk_tc/<decl>.lurk')"

  ARGS:
    decl : String; "Declaration to be typechecked"
]
