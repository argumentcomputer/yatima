import Std.Data.RBMap
import Yatima.Datatypes.Lean
import YatimaStdLib.ByteVector
import Lurk.Field

namespace Yatima.IR

structure Env where
  -- also add metadata
  consts : Std.RBMap Name Lurk.Digest compare
  blocks : Std.RBSet Lurk.Digest compare
  deriving Inhabited

@[inline] def Env.hashes (env : Env) : Array Lurk.Digest :=
  env.consts.valuesArray ++ env.blocks.foldl (·.push ·) #[]

@[inline] def Env.constNames (env : Env) : Std.RBMap Lurk.Digest Name compare :=
  env.consts.foldl (init := .empty) fun acc n f => acc.insert f n

end Yatima.IR
