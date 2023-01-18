import Yatima2.Lean.Utils

namespace Yatima.ContAddr

/-- Errors that can be thrown in `Yatima.ContAddr.ContAddrM` -/
inductive ContAddrError
  | notFoundInCache : Name → ContAddrError
  | notFoundInRecrCtx : Name → ContAddrError
  | invalidConstantIndex : Nat → Nat → ContAddrError
  | unknownConstant : Name → ContAddrError
  | unfilledLevelMetavariable : Lean.Level → ContAddrError
  | unfilledExprMetavariable : Lean.Expr → ContAddrError
  | invalidBVarIndex : Nat → ContAddrError
  | freeVariableExpr : Lean.Expr → ContAddrError
  | metaVariableExpr : Lean.Expr → ContAddrError
  | metaDataExpr : Lean.Expr → ContAddrError
  | levelNotFound : Name → List Name → ContAddrError
  | invalidConstantKind : Name → String → String → ContAddrError
  | constantNotContentAddressed : Name → ContAddrError
  | nonRecursorExtractedFromChildren : Name → ContAddrError
  | cantFindMutDefIndex : Name → ContAddrError
  | custom : String → ContAddrError
  deriving Inhabited

instance : ToString ContAddrError where toString
  | .notFoundInCache n => s!"Could not find cid of '{n}' in cache"
  | .notFoundInRecrCtx n => s!"Could not find '{n}' in recrCtx"
  | .invalidConstantIndex idx size =>
    s!"Invalid index {idx} for dereferring a constant. Must be < {size}."
  | .unknownConstant n => s!"Unknown constant '{n}'"
  | .unfilledLevelMetavariable l => s!"Unfilled level metavariable on universe '{l}'"
  | .unfilledExprMetavariable e => s!"Unfilled level metavariable on expression '{e}'"
  | .invalidBVarIndex idx => s!"Invalid index {idx} for bound variable context"
  | .freeVariableExpr e => s!"Free variable in expression '{e}'"
  | .metaVariableExpr e => s!"Meta variable in expression '{e}'"
  | .metaDataExpr e => s!"Meta data in expression '{e}'"
  | .levelNotFound n ns => s!"'{n}' not found in '{ns}'"
  | .invalidConstantKind n ex gt =>
    s!"Invalid constant kind for '{n}'. Expected '{ex}' but got '{gt}'"
  | .constantNotContentAddressed n => s!"Constant '{n}' wasn't content-addressed"
  | .nonRecursorExtractedFromChildren n =>
    s!"Non-recursor '{n}' extracted from children"
  | .cantFindMutDefIndex n => s!"Can't find index for mutual definition '{n}'"
  | .custom s => s

end Yatima.ContAddr
