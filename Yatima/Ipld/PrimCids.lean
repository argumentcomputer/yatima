import Lean
import Yatima.Typechecker.Datatypes

namespace Yatima.Ipld

open Typechecker

open Std (RBMap) in
def primCidsMap : RBMap String PrimConst compare := .ofList [
  ("bagcyb6egbqlcb6gxj3eegunexxnq6awr3aehcux3tvax5f6uxh5l6c2ntjibn7xr", .nat),
  ("bagcyb6egbqlcauujuov2ffac3lkrkpsjrzlm6k4n6z2pftchjajg3yw74xc3bpvd", .bool),
  ("bagcyb6egbqlcbei23pwlrpzfga6wi56vr7phy7nbwxxblfirmkg42q3uhyvfpsd6", .boolTrue),
  ("bagcyb6egbqlcbn7arbwldqbajrerdu67xibcyjbgp44nuphoeqi7qqa6uiqqjcld", .boolFalse),
  ("bagcyb6egbqlcav6xokynafp5fsz4a2ybhq2octuhvcsrnplpb76fkr4bxpnq7tmy", .natZero),
  ("bagcyb6egbqlcbwowc6i4nuyyusv4fcuqbwgukyuuuro7m7gn6rtx77u25r2typaj", .string),
  ("bagcyb6egbqlcaepbwn7l424zmkewcgcouep6pdfftmougquq3l4elfvviuhxmqjn", .op .natAdd),
  ("bagcyb6egbqlcacycdglvdr774v2izr4ezzzvdpzs2pjasmkht6fdho4j7mnecn3t", .op .natMul),
  ("bagcyb6egbqlcbycyhbsq72njmymsmrdrj7e6b6znlxvhipo2cbv7kigrqtu5xhzu", .op .natPow),
  ("bagcyb6egbqlcacrntpfdoxxf7uq4m7wvjqjttb4z4s5bamhymzhfcol6m47qw2cj", .op .natBeq),
  ("bagcyb6egbqlcbzd254tvrgmz7hr2uvwbevzwiioggkrtqc2wlrofpbvigtvbtgmi", .op .natBle),
  ("bagcyb6egbqlcbtkjghz557gwlb3w4asv5xcrjtr5fpwts32he63p53wnc2lhp3l2", .op .natBlt),
  ("bagcyb6egbqlcbs4ntyq3z35j6hpj5pelkv3xwo2s5737yapedutfqfgd3bzaco5b", .op .natSucc)
] _

-- name: Nat.beq anon: bagcyb6egbqlcacrntpfdoxxf7uq4m7wvjqjttb4z4s5bamhymzhfcol6m47qw2cj
-- name: Nat.ble anon: bagcyb6egbqlcbzd254tvrgmz7hr2uvwbevzwiioggkrtqc2wlrofpbvigtvbtgmi
-- name: Nat.blt anon: bagcyb6egbqlcbtkjghz557gwlb3w4asv5xcrjtr5fpwts32he63p53wnc2lhp3l2
-- name: Bool anon: bagcyb6egbqlcauujuov2ffac3lkrkpsjrzlm6k4n6z2pftchjajg3yw74xc3bpvd
-- name: Bool.true anon: bagcyb6egbqlcbei23pwlrpzfga6wi56vr7phy7nbwxxblfirmkg42q3uhyvfpsd6
-- name: Bool.false anon: bagcyb6egbqlcbn7arbwldqbajrerdu67xibcyjbgp44nuphoeqi7qqa6uiqqjcld
end Yatima.Ipld
