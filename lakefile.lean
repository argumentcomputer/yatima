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
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "3945ff511e73f80a7e675fac1d4972521cd5ccc5"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "e70141d69b8562a0cd31d23a9c9a4f0f90a3c0a6"

lean_exe Tests.CidAnonEqNEq {
  supportInterpreter := true
}
