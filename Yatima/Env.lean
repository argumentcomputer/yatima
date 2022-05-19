import Yatima.Cid
import Yatima.Const

namespace Yatima

open Std (RBMap) in
structure Env where
  univs  : RBMap UnivCid  Univ  Ord.compare
  exprs  : RBMap ExprCid  Expr  Ord.compare
  consts : RBMap ConstCid Const Ord.compare

  univ_anon  : RBMap UnivAnonCid  UnivAnon  Ord.compare
  expr_anon  : RBMap ExprAnonCid  ExprAnon  Ord.compare
  const_anon : RBMap ConstAnonCid ConstAnon Ord.compare

  univ_meta  : RBMap UnivMetaCid  UnivMeta  Ord.compare
  expr_meta  : RBMap ExprMetaCid  ExprMeta  Ord.compare
  const_meta : RBMap ConstMetaCid ConstMeta Ord.compare

end Yatima
