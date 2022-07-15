import Lake

open Lake DSL

package Yatima 

@[defaultTarget]
lean_exe yatima {
  supportInterpreter := true
  root := `Main
}

require Ipld from git
  "https://github.com/yatima-inc/Ipld.lean" @ "ebbba0c92800d35dd59888cf07a0236e4f24e6ed"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "1278c2594eea4a36e51637a376ca764d2866774c"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "80b290a322267aee7dbca96b2547fa24de64236a"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "e70141d69b8562a0cd31d23a9c9a4f0f90a3c0a6"

lean_lib Fixtures {
  roots := #[`Fixtures.AnonCidGroups.ToBeImported]
}

lean_exe Tests.AnonCidGroups { supportInterpreter := true }
lean_exe Tests.Termination   { supportInterpreter := true }
