import Yatima.Datatypes.Const

namespace Yatima

namespace Ipld

open Std (RBMap RBTree) in
/-- The end result of the compilation process -/
structure Store where
  consts : RBTree (Both ConstCid) compare

  univ_anon  : RBMap (UnivCid  .anon) (Univ  .anon) compare
  expr_anon  : RBMap (ExprCid  .anon) (Expr  .anon) compare
  const_anon : RBMap (ConstCid .anon) (Const .anon) compare

  univ_meta  : RBMap (UnivCid  .meta) (Univ  .meta) compare
  expr_meta  : RBMap (ExprCid  .meta) (Expr  .meta) compare
  const_meta : RBMap (ConstCid .meta) (Const .meta) compare
  deriving Inhabited

def Store.union (s s' : Store) : Store := ⟨
  s'.consts.union s.consts,
  s'.univ_anon.fold  (init := s.univ_anon)  fun acc cid x => acc.insert cid x,
  s'.expr_anon.fold  (init := s.expr_anon)  fun acc cid x => acc.insert cid x,
  s'.const_anon.fold (init := s.const_anon) fun acc cid x => acc.insert cid x,
  s'.univ_meta.fold  (init := s.univ_meta)  fun acc cid x => acc.insert cid x,
  s'.expr_meta.fold  (init := s.expr_meta)  fun acc cid x => acc.insert cid x,
  s'.const_meta.fold (init := s.const_meta) fun acc cid x => acc.insert cid x
⟩

end Ipld

structure PureStore where
  consts     : Array Const
  natIdx     : Option Nat
  natZeroIdx : Option Nat
  natSuccIdx : Option Nat
  stringIdx  : Option Nat
  deriving Inhabited

end Yatima
