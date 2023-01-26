import Yatima.Cli.ContAddrCmd
import Yatima.Cli.CommitCmd
-- import Yatima.Cli.TypecheckCmd
-- import Yatima.Cli.CodeGenCmd
-- import Yatima.Cli.ProveCmd
-- import Yatima.Cli.VerifyCmd
-- import Yatima.Cli.IpfsCmd
-- import Yatima.Cli.PrintPrimsCmd

def VERSION : String :=
  s!"{Lean.versionString}|0.0.1"

def yatimaCmd : Cli.Cmd := `[Cli|
  yatima NOOP; [VERSION]
  "A tool for content-addressing and generating Lurk code from Lean 4 code"

  SUBCOMMANDS:
    contAddrCmd;
    commitCmd
    -- typecheckCmd;
    -- codeGenCmd;
    -- proveCmd;
    -- verifyCmd;
    -- ipfsCmd;
    -- printPrimsCmd
]

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    yatimaCmd.printHelp
    return 0
  yatimaCmd.validate args
