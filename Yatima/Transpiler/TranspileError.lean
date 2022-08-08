import Yatima.ForLurkRepo.DSL 
import Yatima.Compiler.Compiler

namespace Yatima.Transpiler 

inductive TranspileError where 
  | notFoundInCache (const : Lurk.Name) : TranspileError
  | invalidConstantKind (const : Const) (ex : String) : TranspileError
  | custom (msg : String) : TranspileError

instance : ToString TranspileError where toString 
  | .notFoundInCache const => s!"{const} not found in cache"
  | .invalidConstantKind const ex => 
    s!"expected {const.name} to be {ex}, but got {const.ctorName}"
  | .custom msg => msg

end Yatima.Transpiler 