import Yatima.Datatypes.Name

namespace Yatima.Typechecker

/- PREVIOUS VERSIONS

inductive TypecheckError where
  | notPi : Value → TypecheckError
  | notTyp : Value → TypecheckError
  | valueMismatch : Value → Value → TypecheckError
  | cannotInferLam : TypecheckError
  | typNotStructure : Value → TypecheckError
  | projEscapesProp : Expr → TypecheckError
  | unsafeDefinition : TypecheckError
  | hasNoRecursionRule : TypecheckError
  | cannotApply : TypecheckError
  | outOfRangeError : Name → Nat → Nat → TypecheckError
  | outOfContextRange : Name → Nat → Nat → TypecheckError
  | outOfDefnRange : Name → Nat → Nat → TypecheckError
  | impossible : TypecheckError
  | custom : String → TypecheckError
  deriving Inhabited

instance : ToString TypecheckError where
  toString 
  | .notPi val => s!"Expected a pi type, found {printVal val}"
  | .notTyp val => s!"Expected a sort type, found {printVal val}"
  | .valueMismatch val₁ val₂ => s!"Expected a {printVal val₁}, found {printVal val₂}"
  | .cannotInferLam .. => "Cannot infer the type of a lambda term"
  | .typNotStructure val => s!"Expected a structure type, found {printVal val}"
  | .projEscapesProp term => s!"Projection {printExpr term} not allowed"
  | .unsafeDefinition .. => "Unsafe definition found"
  | .hasNoRecursionRule .. => "Constructor has no associated recursion rule. Implementation is broken."
  | .cannotApply .. => "Cannot apply argument list to type. Implementation broken."
  | .outOfRangeError name idx len => s!"'{name}' (index {idx}) out of the thunk list range (size {len})"
  | .outOfDefnRange name idx len => s!"'{name}' (index {idx}) out of the range of definitions (size {len})"
  | .outOfContextRange name idx len => s!"'{name}' (index {idx}) out of context range (size {len})"
  | .impossible .. => "Impossible case. Implementation broken."
  | .custom str => str
-/

inductive TypecheckError where
  | notPi : TypecheckError
  | notTyp : TypecheckError
  | valueMismatch : TypecheckError
  | cannotInferLam : TypecheckError
  | typNotStructure : TypecheckError
  | projEscapesProp : TypecheckError
  | unsafeDefinition : TypecheckError
  -- Unsafe definition found
  | hasNoRecursionRule : TypecheckError
  -- Constructor has no associated recursion rule. Implementation is broken.
  | cannotApply : TypecheckError
  -- Cannot apply argument list to type. Implementation broken.
  | impossibleEqualCase : TypecheckError
  -- Impossible equal case
  | impossibleProjectionCase : TypecheckError
  -- Impossible case on projections
  | impossibleEvalCase : TypecheckError
  -- Cannot evaluate this quotient
  | cannotEvalQuotient : TypecheckError
  -- Unknown constant name
  | unknownConst : TypecheckError
  -- No way to extract a name
  | noName : TypecheckError
  | evalError : TypecheckError
  | impossible : TypecheckError
  | outOfRangeError : Name → Nat → Nat → TypecheckError
  | outOfContextRange : Name → Nat → Nat → TypecheckError
  | outOfDefnRange : Name → Nat → Nat → TypecheckError
  | custom : String → TypecheckError
  deriving Inhabited

instance : ToString TypecheckError where
  toString 
  | .notPi => s!"Expected a pi type"
  | .notTyp => s!"Expected a sort type"
  | .valueMismatch => s!"Value mismatch"
  | .cannotInferLam => "Cannot infer the type of a lambda term"
  | .typNotStructure => s!"Expected a structure type"
  | .projEscapesProp => s!"Projection not allowed"
  | .unsafeDefinition .. => "Unsafe definition found"
  | .hasNoRecursionRule .. => "Constructor has no associated recursion rule. Implementation is broken."
  | .cannotApply .. => "Cannot apply argument list to type. Implementation broken."
  | .outOfRangeError name idx len => s!"'{name}' (index {idx}) out of the thunk list range (size {len})"
  | .outOfDefnRange name idx len => s!"'{name}' (index {idx}) out of the range of definitions (size {len})"
  | .outOfContextRange name idx len => s!"'{name}' (index {idx}) out of context range (size {len})"
  | .impossible .. => "Impossible case. Implementation broken."
  | .custom str => str
  | _ => "TODO"

end Yatima.Typechecker
