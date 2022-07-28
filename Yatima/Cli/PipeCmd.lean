import Cli
import Yatima.Cli.Version

-- TODO
def pipeCmd : Cli.Cmd := `[Cli|
  pipe NOOP; [VERSION]
  "Generate Lurk code from Lean code without saving Yatima IR to disk"
]
