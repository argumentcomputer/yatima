import Lake

open Lake DSL

package Yatima 

@[defaultTarget]
lean_exe yatima {
  supportInterpreter := true
  root := `Main
}

require Ipld from git
  "https://github.com/yatima-inc/Ipld.lean" @ "86a04cccf02946181bcf6409a95eb3b2c457a18c"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "0222cb5a6543283dc3c40c7ccd401cb54609d3d0"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "80b290a322267aee7dbca96b2547fa24de64236a"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "e70141d69b8562a0cd31d23a9c9a4f0f90a3c0a6"

lean_exe Tests.AnonCidGroups { supportInterpreter := true }
lean_exe Tests.Termination   { supportInterpreter := true }
