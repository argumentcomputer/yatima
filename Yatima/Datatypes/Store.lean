import Yatima.Datatypes.Const
import Std.Data.RBMap
import Lurk.Scalar.Hashing.Encoding

namespace Yatima

open Std (RBMap)
open IR
open Lurk Scalar

structure Yatima.Store where
  irUnivAnon   : RBMap Hash UnivAnon  compare
  irUnivMeta   : RBMap Hash UnivMeta  compare
  irExprAnon   : RBMap Hash ExprAnon  compare
  irExprMeta   : RBMap Hash ExprMeta  compare
  irConstAnon  : RBMap Hash ConstAnon compare
  irConstMeta  : RBMap Hash ConstMeta compare
  irMetaToAnon : RBMap Hash Hash compare

  tcUnivCache  : RBMap Hash TC.Univ compare
  tcExprCache  : RBMap Hash TC.Expr compare
  tcConstCache : RBMap Hash TC.Const compare

  commitCache : RBMap TC.Const F compare
  encodeState : EncodeState

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
