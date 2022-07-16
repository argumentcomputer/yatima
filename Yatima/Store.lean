import Yatima.Cid
import Yatima.Const

namespace Yatima

open Std (RBMap) in
structure Store where
  univ_cache  : RBMap (UnivCid .Pure) (Univ .Pure) compare
  expr_cache  : RBMap (ExprCid .Pure) (Expr .Pure) compare
  const_cache : RBMap (ConstCid .Pure) (Const .Pure) compare

  univ_anon  : RBMap (UnivCid .Anon) (Univ .Anon)  compare
  expr_anon  : RBMap (ExprCid .Anon) (Expr .Anon)  compare
  const_anon : RBMap (ConstCid .Anon) (Const .Anon) compare

  univ_meta  : RBMap (UnivCid .Meta) (Univ .Meta)  compare
  expr_meta  : RBMap (ExprCid .Meta) (Expr .Meta)  compare
  const_meta : RBMap (ConstCid .Meta) (Const .Meta) compare

instance : Inhabited Store where
  default := ⟨
    .empty, .empty, .empty,
    .empty, .empty, .empty,
    .empty, .empty, .empty
  ⟩

def Store.union (s s' : Store) : Store := ⟨
  s'.univ_cache.fold  (init := s.univ_cache)  fun acc cid x => acc.insert cid x,
  s'.expr_cache.fold  (init := s.expr_cache)  fun acc cid x => acc.insert cid x,
  s'.const_cache.fold (init := s.const_cache) fun acc cid x => acc.insert cid x,
  s'.univ_anon.fold   (init := s.univ_anon)   fun acc cid x => acc.insert cid x,
  s'.expr_anon.fold   (init := s.expr_anon)   fun acc cid x => acc.insert cid x,
  s'.const_anon.fold  (init := s.const_anon)  fun acc cid x => acc.insert cid x,
  s'.univ_meta.fold   (init := s.univ_meta)   fun acc cid x => acc.insert cid x,
  s'.expr_meta.fold   (init := s.expr_meta)   fun acc cid x => acc.insert cid x,
  s'.const_meta.fold  (init := s.const_meta)  fun acc cid x => acc.insert cid x
⟩

end Yatima
