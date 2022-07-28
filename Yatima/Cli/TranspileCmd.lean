import Cli
import Yatima.Cli.Version

-- TODO
def transpileCmd : Cli.Cmd := `[Cli|
  transpile NOOP; [VERSION]
  "Transpile Yatima IR to Lurk code"
]
