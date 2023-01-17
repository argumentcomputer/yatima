import Yatima2.Datatypes.Const
import Std.Data.RBMap

namespace Yatima

open Std (RBMap)

open IR Lurk

structure Yatima.Store where
  irUnivAnon   : RBMap Hash IR.UnivAnon   compare
  irUnivMeta   : RBMap Hash IR.UnivMeta   compare
  irExprAnon   : RBMap Hash IR.ExprAnon   compare
  irExprMeta   : RBMap Hash IR.ExprMeta   compare
  irConstAnon  : RBMap Hash IR.ConstAnon  compare
  irConstMeta  : RBMap Hash IR.ConstMeta  compare
  irMetaToAnon : RBMap Hash Hash compare

  lurkCache    : RBMap LDON F compare
  lurkUnivMap  : RBMap Hash (F × LDON) compare
  lurkExprMap  : RBMap Hash (F × LDON) compare
  lurkConstMap : RBMap Hash (F × LDON) compare

  tcUniv  : RBMap F TC.Univ compare
  tcExpr  : RBMap F TC.Expr compare
  tcConst : RBMap F TC.Const compare

structure Yatima.Env where
  -- meta   : -- hold information about the content-addressing session
  consts : RBMap Name (Hash × Hash) compare

structure TC.Store where
  univ  : RBMap F Univ compare
  expr  : RBMap F Expr compare
  const : RBMap F Const compare

end Yatima
