import Batteries.Data.RBMap
import Yatima.Datatypes.Lean
import YatimaStdLib.ByteVector
import Lurk.Field

namespace Yatima.IR

structure Env where
  -- also add metadata
  consts : Batteries.RBMap Name Lurk.Digest compare
  blocks : Batteries.RBSet Lurk.Digest compare
  deriving Inhabited

@[inline] def Env.hashes (env : Env) : Array Lurk.Digest :=
  env.consts.valuesArray ++ env.blocks.foldl (·.push ·) #[]

@[inline] def Env.constNames (env : Env) : Batteries.RBMap Lurk.Digest Name compare :=
  env.consts.foldl (init := .empty) fun acc n f => acc.insert f n

end Yatima.IR
