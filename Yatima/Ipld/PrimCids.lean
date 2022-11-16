import Lean
import Yatima.Typechecker.Datatypes

namespace Yatima.Ipld

open Typechecker

open Std (RBMap) in
def primCidsMap : RBMap String PrimConst compare := .ofList [
  ("bagcyb6egbqlcb6gxj3eegunexxnq6awr3aehcux3tvax5f6uxh5l6c2ntjibn7xr", .nat),
  ("bagcyb6egbqlcbl2aoqykz65ocaamdlnkpvevymxnfa45koftxu2sbpz4xspk62im", .decT),
  ("bagcyb6egbqlcbhccl4jn32q3kyguwzpohldvsxe5wlyvcbmsmu7mrqgt5byyt6ft", .decF),
  ("bagcyb6egbqlcav6xokynafp5fsz4a2ybhq2octuhvcsrnplpb76fkr4bxpnq7tmy", .natZero),
  ("bagcyb6egbqlcbwowc6i4nuyyusv4fcuqbwgukyuuuro7m7gn6rtx77u25r2typaj", .string),
  ("bagcyb6egbqlcaepbwn7l424zmkewcgcouep6pdfftmougquq3l4elfvviuhxmqjn", .op .natAdd),
  ("bagcyb6egbqlcacycdglvdr774v2izr4ezzzvdpzs2pjasmkht6fdho4j7mnecn3t", .op .natMul),
  ("bagcyb6egbqlcbycyhbsq72njmymsmrdrj7e6b6znlxvhipo2cbv7kigrqtu5xhzu", .op .natPow),
  ("bagcyb6egbqlcbwpderz2lur3hiotv2m2s73xn374xyckvnhrkjfp4zqdzcexzw6p", .op .natDecLe),
  ("bagcyb6egbqlcayltagcmbr7u6dcdfcyzokuke56i5vwesmiqxbevltnd44rfqwjg", .op .natDecLt),
  ("bagcyb6egbqlcb2lqevfndcfelyki2edccpxvobldmj24j6maun7mghs4ylbrsw6x", .op .natDecEq),
  ("bagcyb6egbqlcbs4ntyq3z35j6hpj5pelkv3xwo2s5737yapedutfqfgd3bzaco5b", .op .natSucc)
] _

end Yatima.Ipld
