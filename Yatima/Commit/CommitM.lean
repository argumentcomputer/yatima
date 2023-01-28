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

/--
`RecrCtx` contains information for the reconstruction of (mutual) definitions
and inductives. Each item (identified by an index) in the recursive context is
mapped to its constant index and its name. In the case of definitions, the items
are also identified by a second index that indicates their position among weakly
equal definitions.
-/
abbrev RecrCtx := RBMap (Nat × Option Nat) (Nat × Name) compare

structure CommitCtx where
  store   : StoreAnon
  recrCtx : RecrCtx
  quick   : Bool
  persist : Bool

abbrev CommitM := ReaderT CommitCtx $ ExceptT String $ StateT CommitState IO

/-- Runs a computation with a certain `RecrCtx` -/
def withRecrs (recrCtx : RecrCtx) : CommitM α → CommitM α :=
  withReader $ fun e => { e with recrCtx }

end Yatima.Commit
