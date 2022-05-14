import Yatima.Cid

open Std.RBMap

namespace Yatima

structure Env where
  univs : Std.RBMap UnivCid Univ Ord.compare
  exprs : Std.RBMap ExprCid Expr Ord.compare
  consts : Std.RBMap ConstCid Const Ord.compare

  univ_anon : Std.RBMap UnivAnonCid UnivAnon Ord.compare
  expr_anon : Std.RBMap ExprAnonCid ExprAnon Ord.compare
  const_anon : Std.RBMap ConstAnonCid ConstAnon Ord.compare

  univ_meta : Std.RBMap UnivMetaCid UnivMeta Ord.compare
  expr_meta : Std.RBMap ExprMetaCid ExprMeta Ord.compare
  const_meta : Std.RBMap ConstMetaCid ConstMeta Ord.compare

end Yatima
