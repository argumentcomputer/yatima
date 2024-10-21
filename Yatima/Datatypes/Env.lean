import Batteries.Data.RBMap
import Yatima.Datatypes.Lean
import YatimaStdLib.ByteVector
import Lurk.Field

namespace Yatima.IR

structure Env where
  -- also add metadata
  consts : Batteries.RBMap Name Lurk.F compare
  blocks : Batteries.RBSet Lurk.F compare
  deriving Inhabited

@[inline] def Env.hashes (env : Env) : Array Lurk.F :=
  env.consts.valuesArray ++ env.blocks.foldl (·.push ·) #[]

@[inline] def Env.constNames (env : Env) : Batteries.RBMap Lurk.F Name compare :=
  env.consts.foldl (init := .empty) fun acc n f => acc.insert f n

end Yatima.IR
