import Lake

open Lake DSL

package Yatima 

@[defaultTarget]
lean_exe yatima {
  supportInterpreter := true
  root := "Main"
}

require Ipld from git "https://github.com/yatima-inc/Ipld.lean"@"39d5e0851c5ecffc5eaf501bd090451ceb0da54b"
require LSpec from git "https://github.com/yatima-inc/LSpec.git"@"95b36c3a13e32355a9222e1dad33e354c604798d"
require YatimaStdLib from git "https://github.com/yatima-inc/YatimaStdLib.lean"@"35aecd8951778f45a47d12376635c26a815dcb25"
require Cli from git "https://github.com/mhuisi/lean4-cli"@"e70141d69b8562a0cd31d23a9c9a4f0f90a3c0a6"

lean_exe Tests.CidAnonEqNEq {
  supportInterpreter := true
}
