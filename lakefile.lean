import Lake

open Lake DSL

package Yatima 

@[defaultTarget]
lean_exe yatima {
  supportInterpreter := true
  root := `Main
}

require Ipld from git
  "https://github.com/yatima-inc/Ipld.lean" @ "fceb5347c88f122961902e38764bc4010aafd3c1"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "3b759f6e7798fdb6b17ae83ea060cd34e89b7e91"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "80b290a322267aee7dbca96b2547fa24de64236a"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "e70141d69b8562a0cd31d23a9c9a4f0f90a3c0a6"

lean_lib Fixtures {
  roots := #[`Fixtures.AnonCidGroups.ToBeImported]
}

lean_exe Tests.AnonCidGroups { supportInterpreter := true }
lean_exe Tests.Termination   { supportInterpreter := true }
