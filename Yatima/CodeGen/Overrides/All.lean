import Yatima.CodeGen.Overrides.Array
import Yatima.CodeGen.Overrides.Bool
import Yatima.CodeGen.Overrides.ByteArray
import Yatima.CodeGen.Overrides.Char
import Yatima.CodeGen.Overrides.Fin
import Yatima.CodeGen.Overrides.HashMap
import Yatima.CodeGen.Overrides.Int
import Yatima.CodeGen.Overrides.List
import Yatima.CodeGen.Overrides.Miscellaneous
import Yatima.CodeGen.Overrides.Name
import Yatima.CodeGen.Overrides.Nat
import Yatima.CodeGen.Overrides.String
import Yatima.CodeGen.Overrides.Thunk
import Yatima.CodeGen.Overrides.Typechecker
import Yatima.CodeGen.Overrides.UInt

namespace Lurk.Overrides

def All.module :=
  Array.module ++
  Bool.module ++
  ByteArray.module ++
  Char.module ++
  Fin.module ++
  HashMap.module ++
  Int.module ++
  List.module ++
  Miscellaneous.module ++
  Lean.Name.module ++
  Nat.module ++
  String.module ++
  Thunk.module ++
  Yatima.Typechecker.module ++
  UInt.module

end Lurk.Overrides
