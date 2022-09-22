import Ipld.Cid
import Ipld.Ipld
import Ipld.DagCbor
import Ipld.Multihash
import Yatima.Datatypes.Store

namespace Yatima

namespace Ipld

def univCidFromIpld : Ipld → Option (UnivCid k) := sorry

def univAnonFromIpld : Ipld → Option (Univ .anon)
  | .array #[.number $ Ipld.UNIV .anon, .number 0] =>
    return .zero
  | .array #[.number $ Ipld.UNIV .anon, .number 1, p] =>
    return .succ (← univCidFromIpld p)
  | .array #[.number $ Ipld.UNIV .anon, .number 2, a, b] =>
    return .max (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number $ Ipld.UNIV .anon, .number 3, a, b] =>
    return .imax (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number $ Ipld.UNIV .anon, .number 4, n] => sorry
  | _ => none

def univMetaFromIpld : Ipld → Option (Univ .meta)
  | .array #[.number $ Ipld.UNIV .meta, .number 0] => some .zero
  | .array #[.number $ Ipld.UNIV .meta, .number 1, p] =>
    return .succ (← univCidFromIpld p)
  | .array #[.number $ Ipld.UNIV .meta, .number 2, a, b] =>
    return .max (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number $ Ipld.UNIV .meta, .number 3, a, b] =>
    return .imax (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number $ Ipld.UNIV .meta, .number 4, n] => sorry
  | _ => none

def exprAnonFromIpld : Ipld → Option (Expr .anon)
  | .array #[.number $ Ipld.EXPR .anon, .number 0, n, i, ls] => sorry
  | .array #[.number $ Ipld.EXPR .anon, .number 1, u] => sorry
  | .array #[.number $ Ipld.EXPR .anon, .number 2, n, c, ls] => sorry
  | .array #[.number $ Ipld.EXPR .anon, .number 3, f, a] => sorry
  | .array #[.number $ Ipld.EXPR .anon, .number 4, n, i, d, b] => sorry
  | .array #[.number $ Ipld.EXPR .anon, .number 5, n, i, d, c] => sorry
  | .array #[.number $ Ipld.EXPR .anon, .number 6, n, t, v, b] => sorry
  | .array #[.number $ Ipld.EXPR .anon, .number 7, l] => sorry
  | .array #[.number $ Ipld.EXPR .anon, .number 8, n, e] => sorry
  | _ => none

def exprMetaFromIpld : Ipld → Option (Expr .meta)
  | .array #[.number $ Ipld.EXPR .meta, .number 0, n, i, ls] => sorry
  | .array #[.number $ Ipld.EXPR .meta, .number 1, u] => sorry
  | .array #[.number $ Ipld.EXPR .meta, .number 2, n, c, ls] => sorry
  | .array #[.number $ Ipld.EXPR .meta, .number 3, f, a] => sorry
  | .array #[.number $ Ipld.EXPR .meta, .number 4, n, i, d, b] => sorry
  | .array #[.number $ Ipld.EXPR .meta, .number 5, n, i, d, c] => sorry
  | .array #[.number $ Ipld.EXPR .meta, .number 6, n, t, v, b] => sorry
  | .array #[.number $ Ipld.EXPR .meta, .number 7, l] => sorry
  | .array #[.number $ Ipld.EXPR .meta, .number 8, n, e] => sorry
  | _ => none

def constAnonFromIpld : Ipld → Option (Const .anon)
  | .array #[.number $ Ipld.CONST .anon, .number 0, n, l, t, s] => sorry
  | .array #[.number $ Ipld.CONST .anon, .number 1, n, l, t, v] => sorry
  | .array #[.number $ Ipld.CONST .anon, .number 2, n, l, t, v, s] => sorry
  | .array #[.number $ Ipld.CONST .anon, .number 3, n, l, t, K] => sorry
  | .array #[.number $ Ipld.CONST .anon, .number 5, n, l, t, b, i] => sorry
  | .array #[.number $ Ipld.CONST .anon, .number 6, n, l, t, b, i, j] => sorry
  | .array #[.number $ Ipld.CONST .anon, .number 7, n, l, t, b, i, j] => sorry
  | .array #[.number $ Ipld.CONST .anon, .number 8, n, l, t, b, i] => sorry
  | .array #[.number $ Ipld.CONST .anon, .number 9, b] => sorry
  | .array #[.number $ Ipld.CONST .anon, .number 10, b] => sorry
  | _ => none

def constMetaFromIpld : Ipld → Option (Const .meta)
  | .array #[.number $ Ipld.CONST .meta, .number 0, n, l, t, s] => sorry
  | .array #[.number $ Ipld.CONST .meta, .number 1, n, l, t, v] => sorry
  | .array #[.number $ Ipld.CONST .meta, .number 2, n, l, t, v, s] => sorry
  | .array #[.number $ Ipld.CONST .meta, .number 3, n, l, t, K] => sorry
  | .array #[.number $ Ipld.CONST .meta, .number 5, n, l, t, b, i] => sorry
  | .array #[.number $ Ipld.CONST .meta, .number 6, n, l, t, b, i, j] => sorry
  | .array #[.number $ Ipld.CONST .meta, .number 7, n, l, t, b, i, j] => sorry
  | .array #[.number $ Ipld.CONST .meta, .number 8, n, l, t, b, i] => sorry
  | .array #[.number $ Ipld.CONST .meta, .number 9, b] => sorry
  | .array #[.number $ Ipld.CONST .meta, .number 10, b] => sorry
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
  | .array #[.number Ipld.STORE] => sorry
  | _ => none

end Ipld

end Yatima
