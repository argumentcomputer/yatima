import Lake

open Lake DSL

package Yatima 

@[defaultTarget]
lean_exe yatima {
  supportInterpreter := true
  root := `Main
}

require Ipld from git
  "https://github.com/yatima-inc/Ipld.lean" @ "510a38ee49ca4e496d7a89f285ce74ba77c31e66"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "95f4f5b865a5ac8044fc3c9c2c83a7220f806d4c"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "80b290a322267aee7dbca96b2547fa24de64236a"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "e70141d69b8562a0cd31d23a9c9a4f0f90a3c0a6"

lean_lib Fixtures {
  roots := #[`Fixtures.AnonCidGroups.ToBeImported]
}

lean_exe Tests.AnonCidGroups { supportInterpreter := true }
lean_exe Tests.Termination   { supportInterpreter := true }
