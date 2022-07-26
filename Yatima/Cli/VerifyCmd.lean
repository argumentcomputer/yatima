import Cli
import Yatima.Cli.Version

-- TODO
def verifyCmd : Cli.Cmd := `[Cli|
  verify NOOP; [VERSION]
  "Verify correctness of a Lurk proof"
]
