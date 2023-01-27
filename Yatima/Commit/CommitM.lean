import Std.Data.RBMap
import Yatima.Datatypes.Const
import Yatima.Common.Store

namespace Yatima.Commit

open Std (RBMap)
open IR TC Lurk
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

abbrev CommitM := ReaderT StoreAnon $ ExceptT String $ StateT CommitState IO

end Yatima.Commit
