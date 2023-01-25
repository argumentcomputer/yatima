import Yatima.Datatypes.Univ
import Std.Data.RBMap

namespace Yatima

structure IR.Env where
  -- meta : add information about the content-addressing session
  consts : Std.RBMap Name (Hash × Hash) compare
  deriving Inhabited

end Yatima
