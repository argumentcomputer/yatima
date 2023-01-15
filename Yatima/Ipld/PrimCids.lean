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
  ("baebrmigbs4hyvzg2l5v7kzebkpght76i5kapk6hdea5744lzbqihkhkpky", .op .natBlt),
  ("baebrmigdzoylspjvdmyddnw5ana2akmkqy2p3ek2we7wjz6rj256bnks3i", .op .natSucc)
] _

end Yatima.Ipld
