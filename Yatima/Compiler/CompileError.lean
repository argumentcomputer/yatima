import Yatima.Compiler.Utils
import Yatima.Datatypes.Name
import Yatima.Datatypes.Const

namespace Yatima.Compiler

/-- Errors that can be thrown in `Yatima.Compiler.CompileM` -/
inductive CompileError
  | notFoundInCache : Name → CompileError
  | notFoundInRecrCtx : Name → CompileError
  | invalidDereferringIndex : Nat → Nat → CompileError
  | unknownConstant : Name → CompileError
  | unfilledLevelMetavariable : Lean.Level → CompileError
  | unfilledExprMetavariable : Lean.Expr → CompileError
  | invalidBVarIndex : Nat → CompileError
  | freeVariableExpr : Lean.Expr → CompileError
  | metaVariableExpr : Lean.Expr → CompileError
  | metaDataExpr : Lean.Expr → CompileError
  | levelNotFound : Name → List Name → CompileError
  | invalidConstantKind : Lean.ConstantInfo → String → CompileError
  | invalidConstantKind' : Const → String → CompileError
  | constantNotCompiled : Lean.Name → CompileError
  | nonRecursorExtractedFromChildren : Lean.Name → CompileError
  | cantFindMutDefIndex : Lean.Name → CompileError
  | errorsOnFile : String → String → CompileError
  | custom : String → CompileError
  deriving Inhabited

instance : ToString CompileError where toString
  | .notFoundInCache n => s!"Could not find cid of '{n}' in cache"
  | .notFoundInRecrCtx n => s!"Could not find '{n}' in recrCtx"
  | .invalidDereferringIndex idx size =>
    s!"Invalid index {idx} for dereferring a constant. Must be < {size}."
  | .unknownConstant n => s!"Unknown constant '{n}'"
  | .unfilledLevelMetavariable l => s!"Unfilled level metavariable on universe '{l}'"
  | .unfilledExprMetavariable e => s!"Unfilled level metavariable on expression '{e}'"
  | .invalidBVarIndex idx => s!"Invalid index {idx} for bound variable context"
  | .freeVariableExpr e => s!"Free variable in expression '{e}'"
  | .metaVariableExpr e => s!"Meta variable in expression '{e}'"
  | .metaDataExpr e => s!"Meta data in expression '{e}'"
  | .levelNotFound n ns => s!"'{n}' not found in '{ns}'"
  | .invalidConstantKind c ex =>
    s!"Invalid constant kind for '{c.name}'. Expected '{ex}' but got '{c.ctorName}'"
  | .invalidConstantKind' c ex =>
    s!"Invalid constant kind for '{c.name}'. Expected '{ex}' but got '{c.ctorName}'"
  | .constantNotCompiled n => s!"Constant '{n}' wasn't compiled"
  | .nonRecursorExtractedFromChildren n =>
    s!"Non-recursor '{n}' extracted from children"
  | .cantFindMutDefIndex n => s!"Can't find index for mutual definition '{n}'"
  | .errorsOnFile file err => s!"Errors on file {file}:\n\n{err}"
  | .custom s => s

end Yatima.Compiler
