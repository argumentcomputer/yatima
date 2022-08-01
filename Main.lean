import Yatima.Cli.CompileCmd
import Yatima.Cli.TypecheckCmd
import Yatima.Cli.TranspileCmd
import Yatima.Cli.PipeCmd
import Yatima.Cli.ProveCmd
import Yatima.Cli.VerifyCmd

opaque VERSION : String :=
  s!"{Lean.versionString}|0.0.1"

def yatimaCmd : Cli.Cmd := `[Cli|
  yatima NOOP; [VERSION]
  "A compiler and typechecker for the Yatima language"

  SUBCOMMANDS:
    compileCmd;
    typecheckCmd;
    transpileCmd;
    pipeCmd;
    proveCmd;
    verifyCmd
]

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    yatimaCmd.printHelp
    return 0
  yatimaCmd.validate args
