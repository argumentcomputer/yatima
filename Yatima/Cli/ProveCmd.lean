import Cli
import Yatima.Cli.Version

-- TODO
def proveCmd : Cli.Cmd := `[Cli|
  prove NOOP; [VERSION]
  "Generate a Lurk proof from a Lean declaration"
]
