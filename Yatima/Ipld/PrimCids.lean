import Std.Data.RBMap
import Yatima.Typechecker.Datatypes

namespace Yatima.Ipld

open Typechecker

open Std (RBMap) in
def primCidsMap : RBMap String PrimConst compare := .ofList [
  ("baebrmidyeaf7ya6r32orixinrc7d4airdgqj6yu2uu7ysnlkm6tm6oyfmq", .nat),
  ("baebrmidhmcsklgytqdkylk3lknuebhzxlciw24ngwiefvbprxvssvganzq", .bool),
  ("baebrmie32rtlug65hqhxuvhj4jm5vn7pyx5ns2wlgua7xqpktcg7r5vxr4", .boolTrue),
  ("baebrmifgymcid753glhyh5ip2ei5gyo4cznlnaococvufgcpykfmkw4jvm", .boolFalse),
  ("baebrmib2egquvcrpxjbutetjyierihjxwwopifr2i5wsctleidtnjrmqsu", .natZero),
  ("baebrmig4kd2lhvpdpjpz3oz75xptjrvlqrhdl6eowj5s7vdvyfv64q5v2q", .string),
  ("baebrmichjhv5idpe5nhefr2icmxq6peoy7zedfcrau2xode4k6owqmp2pu", .op .natAdd),
  ("baebrmib52s6333ze2edgrym7lgsqwuqaogx2dookrwkzjkwwffbquf7n6q", .op .natMul),
  ("baebrmicjxbl3f7lsyir65tt5osbwtyagncxjumkh4g2oz6pm7dgyy6267a", .op .natPow),
  ("baebrmiag3pffbbxzpgoaexjfktbhkebnfrkbsvuetpopu5ahcdtaigjzoi", .op .natBeq),
  ("baebrmiacffb3dg5jj27qntdbrnoaufkacmoortyrmsi5vng5uq5qajela4", .op .natBle),
  ("bagcyb6egbqlcbtkjghz557gwlb3w4asv5xcrjtr5fpwts32he63p53wnc2lhp3l2", .op .natBlt), -- TODO update me
  ("baebrmigdzoylspjvdmyddnw5ana2akmkqy2p3ek2we7wjz6rj256bnks3i", .op .natSucc)
] _

-- name: Nat.beq anon: bagcyb6egbqlcacrntpfdoxxf7uq4m7wvjqjttb4z4s5bamhymzhfcol6m47qw2cj
-- name: Nat.ble anon: bagcyb6egbqlcbzd254tvrgmz7hr2uvwbevzwiioggkrtqc2wlrofpbvigtvbtgmi
-- name: Nat.blt anon: bagcyb6egbqlcbtkjghz557gwlb3w4asv5xcrjtr5fpwts32he63p53wnc2lhp3l2
-- name: Bool anon: bagcyb6egbqlcauujuov2ffac3lkrkpsjrzlm6k4n6z2pftchjajg3yw74xc3bpvd
-- name: Bool.true anon: bagcyb6egbqlcbei23pwlrpzfga6wi56vr7phy7nbwxxblfirmkg42q3uhyvfpsd6
-- name: Bool.false anon: bagcyb6egbqlcbn7arbwldqbajrerdu67xibcyjbgp44nuphoeqi7qqa6uiqqjcld
end Yatima.Ipld
