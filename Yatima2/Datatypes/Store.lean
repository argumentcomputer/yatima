import Yatima2.Datatypes.Const
import Std.Data.RBMap

namespace Yatima

open Std (RBMap)

open IR Lurk

structure Yatima.Store where
  irUnivAnon   : RBMap Hash IR.UnivAnon  compare
  irUnivMeta   : RBMap Hash IR.UnivMeta  compare
  irExprAnon   : RBMap Hash IR.ExprAnon  compare
  irExprMeta   : RBMap Hash IR.ExprMeta  compare
  irConstAnon  : RBMap Hash IR.ConstAnon compare
  irConstMeta  : RBMap Hash IR.ConstMeta compare
  irMetaToAnon : RBMap Hash Hash compare

  lurkLDONCache  : RBMap LDON F compare
  lurkUnivCache  : RBMap Hash LDON compare
  lurkExprCache  : RBMap Hash LDON compare
  lurkConstCache : RBMap Hash (LDON × F) compare

  tcConsts : RBMap F TC.Const compare

structure Yatima.Env where
  -- meta   : -- hold information about the content-addressing session
  consts : RBMap Name (Hash × Hash) compare

structure TC.Store where
  consts : RBMap F Const compare

end Yatima
