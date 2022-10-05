import Yatima.Datatypes.Lean

namespace Yatima.Transpiler 

inductive TranspileError where 
  | notFoundInMap (name : Name) : TranspileError
  | notFoundInStore (name : Name) : TranspileError
  | invalidConstantKind (name : Name) (ex : String) (gt : String) : TranspileError
  | custom (msg : String) : TranspileError

instance : ToString TranspileError where toString 
  | .notFoundInMap name => s!"{name} not found in map"
  | .notFoundInStore name => s!"{name} not found in store"
  | .invalidConstantKind name ex gt => s!"expected {name} to be {ex}, but got {gt}"
  | .custom msg => msg

end Yatima.Transpiler 