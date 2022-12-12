import Yatima.Transpiler.Overrides.Array
import Yatima.Transpiler.Overrides.Bool
import Yatima.Transpiler.Overrides.Char
import Yatima.Transpiler.Overrides.Fin
import Yatima.Transpiler.Overrides.List
import Yatima.Transpiler.Overrides.Miscellaneous
import Yatima.Transpiler.Overrides.Name
import Yatima.Transpiler.Overrides.Nat
import Yatima.Transpiler.Overrides.String
import Yatima.Transpiler.Overrides.UInt

namespace Lurk.Overrides2

def All.module :=
  Array.module ++
  Bool.module ++
  Char.module ++
  Fin.module ++
  List.module ++
  Miscellaneous.module ++
  Name.module ++
  Nat.module ++
  String.module ++
  UInt.module

end Lurk.Overrides2
