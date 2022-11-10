import Lurk.Field
import Std.Data.RBMap.Basic

namespace Yatima.IR

inductive PrimConst
  | nat | natZero | natSucc | string

-- open Std in
-- def primCidsMap : RBMap Lurk.F PrimConst compare := .ofList [
--   (sorry, .nat),
--   (sorry, .natZero),
--   (sorry, .natSucc),
--   (sorry, .string)
-- ] compare

end Yatima.IR
