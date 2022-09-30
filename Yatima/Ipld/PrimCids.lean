import Lean

namespace Yatima.Ipld

inductive PrimConst
  | nat | natZero | natSucc | string

open Std (RBMap) in
def primCidsMap : RBMap String PrimConst compare := .ofList [
  ("bagcyb6egbqlcb6gxj3eegunexxnq6awr3aehcux3tvax5f6uxh5l6c2ntjibn7xr", .nat),
  ("bagcyb6egbqlcav6xokynafp5fsz4a2ybhq2octuhvcsrnplpb76fkr4bxpnq7tmy", .natZero),
  ("bagcyb6egbqlcbs4ntyq3z35j6hpj5pelkv3xwo2s5737yapedutfqfgd3bzaco5b", .natSucc),
  ("bagcyb6egbqlcbwowc6i4nuyyusv4fcuqbwgukyuuuro7m7gn6rtx77u25r2typaj", .string)
]

end Yatima.Ipld
