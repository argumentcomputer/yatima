import Yatima.Const

namespace Yatima

namespace Ipld
open Std (RBMap RBTree) in
structure Store where
  univ_anon  : RBMap (UnivCid .Anon) (Univ .Anon)  compare
  expr_anon  : RBMap (ExprCid .Anon) (Expr .Anon)  compare
  const_anon : RBMap (ConstCid .Anon) (Const .Anon) compare

  univ_meta  : RBMap (Ipld.UnivCid .Meta) (Ipld.Univ .Meta)  compare
  expr_meta  : RBMap (Ipld.ExprCid .Meta) (Ipld.Expr .Meta)  compare
  const_meta : RBMap (Ipld.ConstCid .Meta) (Ipld.Const .Meta) compare

  univ_cids  : RBTree (Both UnivCid) compare
  expr_cids  : RBTree (Both ExprCid) compare
  const_cids  : RBTree (Both ConstCid) compare

instance : Inhabited Store where
  default := ⟨
    .empty, .empty, .empty,
    .empty, .empty, .empty,
    .empty, .empty, .empty
  ⟩

def Store.union (s s' : Store) : Store := ⟨
  s'.univ_anon.fold   (init := s.univ_anon)   fun acc cid x => acc.insert cid x,
  s'.expr_anon.fold   (init := s.expr_anon)   fun acc cid x => acc.insert cid x,
  s'.const_anon.fold  (init := s.const_anon)  fun acc cid x => acc.insert cid x,
  s'.univ_meta.fold   (init := s.univ_meta)   fun acc cid x => acc.insert cid x,
  s'.expr_meta.fold   (init := s.expr_meta)   fun acc cid x => acc.insert cid x,
  s'.const_meta.fold  (init := s.const_meta)  fun acc cid x => acc.insert cid x,
  s'.univ_cids.union   s.univ_cids,
  s'.expr_cids.union   s.expr_cids,
  s'.const_cids.union  s.const_cids
⟩
end Ipld

end Yatima
