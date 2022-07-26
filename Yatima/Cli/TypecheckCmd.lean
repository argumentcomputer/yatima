import Cli
import Yatima.Cli.Version

-- TODO
def typecheckCmd : Cli.Cmd := `[Cli|
  typecheck NOOP; [VERSION]
  "Typecheck Yatima IR"
]
