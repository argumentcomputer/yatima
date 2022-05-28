import Yatima.Cid
import Yatima.Const

namespace Yatima

open Std (RBMap) in
structure Env where
  univ_cache  : RBMap UnivCid  Univ  Ord.compare
  expr_cache  : RBMap ExprCid  Expr  Ord.compare
  const_cache : RBMap ConstCid Const Ord.compare

  univ_anon  : RBMap UnivAnonCid  UnivAnon  Ord.compare
  expr_anon  : RBMap ExprAnonCid  ExprAnon  Ord.compare
  const_anon : RBMap ConstAnonCid ConstAnon Ord.compare

  univ_meta  : RBMap UnivMetaCid  UnivMeta  Ord.compare
  expr_meta  : RBMap ExprMetaCid  ExprMeta  Ord.compare
  const_meta : RBMap ConstMetaCid ConstMeta Ord.compare

instance : Inhabited Env where
  default := ⟨
    .empty, .empty, .empty,
    .empty, .empty, .empty,
    .empty, .empty, .empty
  ⟩

end Yatima
