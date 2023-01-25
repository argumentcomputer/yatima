import Yatima.Datatypes.Const
import Std.Data.RBMap

namespace Yatima

open Std (RBMap)
open IR Lurk

structure Yatima.Store where
  irUnivAnon  : RBMap Hash UnivAnon  compare
  irUnivMeta  : RBMap Hash UnivMeta  compare
  irExprAnon  : RBMap Hash ExprAnon  compare
  irExprMeta  : RBMap Hash ExprMeta  compare
  irConstAnon : RBMap Hash ConstAnon compare
  irConstMeta : RBMap Hash ConstMeta compare

  tcUniv  : RBMap Hash TC.Univ compare
  tcExpr  : RBMap Hash TC.Expr compare
  tcConst : RBMap Hash TC.Const compare

  ldonHashState : LDONHashState -- to speed up committing
  commits : RBMap TC.Const F compare
  deriving Inhabited

structure Yatima.Env where
  -- meta   : -- hold information about the content-addressing session
  irHashes : RBMap Name (Hash × Hash) compare
  tcHashes : RBMap Name F compare
  deriving Inhabited

end Yatima
