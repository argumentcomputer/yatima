import Std.Data.RBMap
import Yatima.Datatypes.Hash
import Yatima.Datatypes.Const

namespace Yatima.Commit

open Std (RBMap)
open IR

structure Store where
  univ  : RBMap Hash UnivAnon  compare
  expr  : RBMap Hash ExprAnon  compare
  const : RBMap Hash ConstAnon compare
  deriving Inhabited

open TC Lurk

structure CommitState where
  univ  : RBMap Hash Univ compare
  expr  : RBMap Hash Expr compare
  const : RBMap Hash Const compare

  ldonHashState : LDONHashState -- to speed up committing
  commits : RBMap Hash F compare
  deriving Inhabited

abbrev CommitM := ReaderT Store $ ExceptT String $ StateT CommitState IO

end Yatima.Commit
