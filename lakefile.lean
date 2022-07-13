import Lake

open Lake DSL

package Yatima 

@[defaultTarget]
lean_exe yatima {
  supportInterpreter := true
  root := `Main
}

require Ipld from git
  "https://github.com/yatima-inc/Ipld.lean" @ "2eb1ae8a0282d52af45d916d240fb0b5ec491ab0"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "95b36c3a13e32355a9222e1dad33e354c604798d"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "877d4fe8d42fbef22cd151efabe7e319bf325e6f"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "e70141d69b8562a0cd31d23a9c9a4f0f90a3c0a6"

lean_exe Tests.CidAnonEqNEq {
  supportInterpreter := true
}
