import Cli.Basic
import Yatima.Cli.Utils
import Yatima.Typechecker.Typechecker

open System Yatima.Typechecker in
def typecheckRun (p : Cli.Parsed) : IO UInt32 := do
  -- Check toolchain
  if !(← validToolchain) then return 1

  -- Get Lean source file name
  let some source := p.positionalArg? "source" |>.map (·.value)
    | IO.eprintln "No source was provided"; return 1

  sorry

def typecheckCmd : Cli.Cmd := `[Cli|
  tc VIA typecheckRun;
  "Typechecks all constants in a Lean file using cheap hashes"

  ARGS:
    source : String; "Lean source file"
]
