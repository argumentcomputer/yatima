import Ipld.Cid
import Ipld.Ipld
import Ipld.DagCbor
import Ipld.Multihash
import Yatima.Datatypes.Store

namespace Yatima

namespace Ipld

def univAnonFromIpld : Ipld → Option (Univ .anon)
  | .array #[.number 0xC0DE0001, .number 0] => sorry
  | _ => none

def univMetaFromIpld : Ipld → Option (Univ .meta)
  | .array #[.number 0xC0DE0002, .number 0] => sorry
  | _ => none

def exprAnonFromIpld : Ipld → Option (Expr .anon)
  | .array #[.number 0xC0DE0003, .number 0, n, i, ls] => sorry
  | _ => none

def exprMetaFromIpld : Ipld → Option (Expr .meta)
  | .array #[.number 0xC0DE0004, .number 0, n, i, ls] => sorry
  | _ => none

def constAnonFromIpld : Ipld → Option (Const .anon)
  | .array #[.number 0xC0DE0005, .number 0, n, l, t, s] => sorry
  | _ => none

def constMetaFromIpld : Ipld → Option (Const .meta)
  | .array #[.number 0xC0DE0006, .number 0, n, l, t, s] => sorry
  | _ => none

def univFromIpld (anon meta : Ipld) : Option $ Both Univ := do
  some ⟨← univAnonFromIpld anon, ← univMetaFromIpld meta⟩

def exprFromIpld (anon meta : Ipld) : Option $ Both Expr := do
  some ⟨← exprAnonFromIpld anon, ← exprMetaFromIpld meta⟩

def constFromIpld (anon meta : Ipld) : Option $ Both Const := do
  some ⟨← constAnonFromIpld anon, ← constMetaFromIpld meta⟩

def bothConstCidFromIpld : Ipld → Option (Both ConstCid)
  | .array #[.string anon, .string meta] => do
    let anon ← Cid.fromString Base.b32.toMultibase anon
    let meta ← Cid.fromString Base.b32.toMultibase meta
    some ⟨⟨anon⟩, ⟨meta⟩⟩
  | _ => none

def storeFromIpld : Ipld → Option Store
  | .array #[.number 0xC0DE0007] => sorry
  | _ => none

end Ipld

end Yatima
