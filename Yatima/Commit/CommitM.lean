import Std.Data.RBMap
import Yatima.Datatypes.Const

namespace Yatima.Commit

open Std (RBMap)
open IR

structure Store where
  univs  : RBMap Hash UnivAnon  compare
  exprs  : RBMap Hash ExprAnon  compare
  consts : RBMap Hash ConstAnon compare
  deriving Inhabited

open TC Lurk
open System (FilePath)

structure CommitState where
  univPaths   : RBMap Hash FilePath compare
  exprPaths   : RBMap Hash FilePath compare
  constPaths  : RBMap Hash FilePath compare
  commitPaths : RBMap Hash FilePath compare

  univs   : RBMap Hash Univ  compare
  exprs   : RBMap Hash Expr  compare
  consts  : RBMap Hash Const compare
  commits : RBMap Hash F     compare

  ldonHashState : LDONHashState -- to speed up committing
  deriving Inhabited

abbrev CommitM := ReaderT Store $ ExceptT String $ StateT CommitState IO

end Yatima.Commit
