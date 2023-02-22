import Std.Data.RBMap
import Yatima.Datatypes.Lean
import Lurk.Field

namespace Yatima

structure IR.Env where
  -- meta : add information about the content-addressing session
  consts : Std.RBMap Name Lurk.F compare
  deriving Inhabited

def IR.Env.hashes (env : IR.Env) : Array Lurk.F :=
  env.consts.valuesArray

end Yatima
