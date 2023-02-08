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

def CommitState.tcStore (stt : CommitState) : RBMap F Const compare :=
  stt.commits.foldl (init := default) fun acc h f =>
    match stt.consts.find? h with
    | some c => acc.insert f c
    | none => acc

structure CommitCtx where
  store   : StoreAnon
  quick   : Bool
  persist : Bool

abbrev CommitM := ReaderT CommitCtx $ ExceptT String $ StateT CommitState IO

end Yatima.Commit
