import Yatima.Transpiler.Overrides.Array
import Yatima.Transpiler.Overrides.Bool
import Yatima.Transpiler.Overrides.ByteArray
import Yatima.Transpiler.Overrides.Char
import Yatima.Transpiler.Overrides.Fin
import Yatima.Transpiler.Overrides.HashMap
import Yatima.Transpiler.Overrides.List
import Yatima.Transpiler.Overrides.Miscellaneous
import Yatima.Transpiler.Overrides.Name
import Yatima.Transpiler.Overrides.Nat
import Yatima.Transpiler.Overrides.String
import Yatima.Transpiler.Overrides.Thunk
import Yatima.Transpiler.Overrides.UInt

namespace Lurk.Overrides

def All.module :=
  Array.module ++
  Bool.module ++
  ByteArray.module ++
  Char.module ++
  Fin.module ++
  HashMap.module ++
  List.module ++
  Miscellaneous.module ++
  Lean.Name.module ++
  Nat.module ++
  String.module ++
  Thunk.module ++
  UInt.module

end Lurk.Overrides
