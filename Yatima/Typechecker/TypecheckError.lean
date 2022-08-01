import Yatima.Datatypes.Name

namespace Yatima.Typechecker

/- PREVIOUS VERSIONS

inductive CheckError where
  | notPi : Value → CheckError
  | notTyp : Value → CheckError
  | valueMismatch : Value → Value → CheckError
  | cannotInferLam : CheckError
  | typNotStructure : Value → CheckError
  | projEscapesProp : Expr → CheckError
  | unsafeDefinition : CheckError
  | hasNoRecursionRule : CheckError
  | cannotApply : CheckError
  | outOfRangeError : Name → Nat → Nat → CheckError
  | outOfContextRange : Name → Nat → Nat → CheckError
  | outOfDefnRange : Name → Nat → Nat → CheckError
  | impossible : CheckError
  | custom : String → CheckError
  deriving Inhabited

instance : ToString CheckError where
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

inductive CheckError where
  | notPi : CheckError
  | notTyp : CheckError
  | valueMismatch : CheckError
  | cannotInferLam : CheckError
  | typNotStructure : CheckError
  | projEscapesProp : CheckError
  | unsafeDefinition : CheckError
  -- Unsafe definition found
  | hasNoRecursionRule : CheckError
  -- Constructor has no associated recursion rule. Implementation is broken.
  | cannotApply : CheckError
  -- Cannot apply argument list to type. Implementation broken.
  | impossibleEqualCase : CheckError
  -- Impossible equal case
  | impossibleProjectionCase : CheckError
  -- Impossible case on projections
  | impossibleEvalCase : CheckError
  -- Cannot evaluate this quotient
  | cannotEvalQuotient : CheckError
  -- Unknown constant name
  | unknownConst : CheckError
  -- No way to extract a name
  | noName : CheckError
  | evalError : CheckError
  | impossible : CheckError
  | outOfRangeError : Name → Nat → Nat → CheckError
  | outOfContextRange : Name → Nat → Nat → CheckError
  | outOfDefnRange : Name → Nat → Nat → CheckError
  | custom : String → CheckError
  deriving Inhabited

instance : ToString CheckError where
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
