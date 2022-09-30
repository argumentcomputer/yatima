import Yatima.ForLurkRepo.DSL 
import Yatima.Compiler.Compiler

namespace Yatima.Transpiler 

inductive TranspileError where 
  | notFoundInMap (name : Name) : TranspileError
  | notFoundInStore (name : Name) : TranspileError
  | invalidConstantKind (const : Const) (ex : String) : TranspileError
  | custom (msg : String) : TranspileError

instance : ToString TranspileError where toString 
  | .notFoundInMap name => s!"{name} not found in map"
  | .notFoundInStore name => s!"{name} not found in store"
  | .invalidConstantKind const ex => 
    s!"expected {const.name} to be {ex}, but got {const.ctorName}"
  | .custom msg => msg

end Yatima.Transpiler 