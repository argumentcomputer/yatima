import Yatima.Cid
import Yatima.Const

namespace Yatima

open Std (RBMap) in
structure Store where
  univ_cache  : RBMap UnivCid  Univ  compare
  expr_cache  : RBMap ExprCid  Expr  compare
  const_cache : RBMap ConstCid Const compare

  univ_anon  : RBMap UnivAnonCid  UnivAnon  compare
  expr_anon  : RBMap ExprAnonCid  ExprAnon  compare
  const_anon : RBMap ConstAnonCid ConstAnon compare

  univ_meta  : RBMap UnivMetaCid  UnivMeta  compare
  expr_meta  : RBMap ExprMetaCid  ExprMeta  compare
  const_meta : RBMap ConstMetaCid ConstMeta compare

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
