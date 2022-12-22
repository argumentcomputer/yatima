import Lean.Compiler.LCNF
import Lean.Util.FoldConsts
import Std.Data.HashMap

open Std

namespace Lean.Compiler.LCNF

def LetValue.getUsedConstant : LetValue → Std.HashSet Name
  | .value _ | .erased | .proj .. | .fvar .. => #[]
  | .const declName .. => #[declName]  

partial def Code.getUsedConstants : Code → Array Name
  | .let decl k => k.getUsedConstants ++ decl.value.getUsedConstant
  | .fun decl k => k.getUsedConstants ++ decl.value.getUsedConstants
  | .jp decl k => k.getUsedConstants ++ decl.value.getUsedConstants
  | .cases cs => cs.alts.concatMap fun alt => alt.getCode.getUsedConstants
  | .jmp .. | .return _ | .unreach _ => #[]

def Decl.getUsedConstants (decl : Decl) : Array Name :=
  let (name, type, value) := (decl.name, decl.type, decl.value)
  value.getUsedConstants ++ type.getUsedConstants ++ #[name]

end Lean.Compiler.LCNF