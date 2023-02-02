import Cli.Basic
import Yatima.Datatypes.Env
import Yatima.Common.IO
import Yatima.Common.LightData
import Yatima.Lean.Utils
import Yatima.CodeGen.CodeGen
import Yatima.Typechecker.Typechecker -- forcing oleans generation

/-- We will need a smarter solution to be shipped in the `yatima` binary -/
def mkTCCode (f : Lurk.F) : String :=
s!"import Yatima.Typechecker.Typechecker
def tc := Yatima.Typechecker.typecheckConstNoStore (.ofNat {f.val})
"

open Yatima.CodeGen in
def proveRun (p : Cli.Parsed) : IO UInt32 := do

  -- Get environment file name
  let some decl := p.positionalArg? "decl" |>.map (·.value.toNameSafe)
    | IO.eprintln "No declaration was provided"; return 1

  -- Load environment
  let some envFileName := p.flag? "env" |>.map (·.value)
    | IO.eprintln "Environment file not provided"; return 1

  let some (env : Yatima.IR.Env) ← loadData envFileName false | return 1
  let some (anonHash, _) := env.consts.find? decl
    | IO.eprintln s!"{decl} not found in the environment"; return 1

  let some (comm : Lurk.F) ← loadData (COMMITSDIR / anonHash.data.toHex) true
    | IO.eprintln s!"Commitment for {decl} not found"; return 1

  let expr ← match codeGen (← Lean.runFrontend (mkTCCode comm) default) "tc" with
  | .error msg => IO.eprintln msg; return 1
  | .ok expr => pure $ if p.hasFlag "anon" then expr.anon else expr

  -- Write Lurk file
  let output := match p.flag? "output" |>.map (·.value) with
    | some output => ⟨output⟩
    | none => "lurk_tc" / s!"{decl}.lurk"
  match output.parent with
  | some dir => if ! (← dir.pathExists) then IO.FS.createDirAll dir
  | none => pure ()
  IO.println s!"Writing output to {output}"
  IO.FS.writeFile output (expr.toString true)

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
