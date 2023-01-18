import Yatima2.Datatypes.Const
import Std.Data.RBMap

namespace Yatima

open Std (RBMap)

open IR Lurk

structure Yatima.Store where
  irUnivAnon   : RBMap Hash UnivAnon  compare
  irUnivMeta   : RBMap Hash UnivMeta  compare
  irExprAnon   : RBMap Hash ExprAnon  compare
  irExprMeta   : RBMap Hash ExprMeta  compare
  irConstAnon  : RBMap Hash ConstAnon compare
  irConstMeta  : RBMap Hash ConstMeta compare
  irMetaToAnon : RBMap Hash Hash compare

  lurkLDONCache  : RBMap LDON F compare
  lurkUnivCache  : RBMap Hash LDON compare
  lurkExprCache  : RBMap Hash LDON compare
  lurkConstCache : RBMap Hash (LDON × F) compare

  tcConsts : RBMap F TC.Const compare
  deriving Inhabited

structure Yatima.Env where
  -- meta   : -- hold information about the content-addressing session
  consts : RBMap Name (Hash × Hash) compare
  deriving Inhabited

structure TC.Store where
  consts : RBMap F Const compare
  deriving Inhabited

end Yatima
