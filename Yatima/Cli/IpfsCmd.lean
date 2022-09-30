import Yatima.Cli.PutCmd
import Yatima.Cli.GetCmd

def ipfsCmd : Cli.Cmd := `[Cli|
  ipfs NOOP;
  "Stores or retrieves a Yatima data store from IPFS"

  SUBCOMMANDS:
    putCmd;
    getCmd
]
