import Std.Data.RBMap
import Yatima.Datatypes.Lean
import YatimaStdLib.ByteVector
import Lurk.Field

namespace Yatima.IR

structure Env where
  consts : Std.RBMap Name Lurk.F compare
  storeName : System.FilePath
  deriving Inhabited

@[inline] def Env.hashes (env : Env) : Array Lurk.F :=
  env.consts.valuesArray

@[inline] def Env.constNames (env : Env) : Std.RBMap Lurk.F Name compare :=
  env.consts.foldl (init := .empty) fun acc n f => acc.insert f n

end Yatima.IR
