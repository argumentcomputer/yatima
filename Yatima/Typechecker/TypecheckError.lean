import Yatima.Datatypes.Name

namespace Yatima.Typechecker

inductive TypecheckError where
  | notPi : String →  TypecheckError
  | notTyp : String → TypecheckError
  | valueMismatch : String → String → TypecheckError
  | cannotInferLam : TypecheckError
  | typNotStructure : String → TypecheckError
  | projEscapesProp : String → TypecheckError
  | unsafeDefinition : TypecheckError
  | hasNoRecursionRule : TypecheckError
  | cannotApply : TypecheckError
  | impossibleEqualCase : TypecheckError
  | impossibleProjectionCase : TypecheckError
  | impossibleEvalCase : TypecheckError
  | cannotEvalQuotient : TypecheckError
  | unknownConst : TypecheckError
  | noName : TypecheckError
  | impossible : TypecheckError
  | outOfRangeError : Name → Nat → Nat → TypecheckError
  | outOfContextRange : Name → Nat → Nat → TypecheckError
  | outOfConstsRange : Name → Nat → Nat → TypecheckError
  | custom : String → TypecheckError
  deriving Inhabited

instance : ToString TypecheckError where toString
  | .notPi val => s!"Expected a pi type, found '{val}'"
  | .notTyp val => s!"Expected a sort type, found '{val}'"
  | .valueMismatch val₁ val₂ => s!"Expected {val₁}, found {val₂}"
  | .cannotInferLam => "Cannot infer the type of a lambda term"
  | .typNotStructure val => s!"Expected a structure type, found {val}"
  | .projEscapesProp term => s!"Projection {term} not allowed"
  | .unsafeDefinition => "Unsafe definition found"
  | .hasNoRecursionRule => "Constructor has no associated recursion rule. Implementation is broken."
  | .cannotApply => "Cannot apply argument list to type. Implementation broken."
  | .outOfRangeError name idx len => s!"'{name}' (index {idx}) out of the thunk list range (size {len})"
  | .outOfConstsRange name idx len => s!"'{name}' (index {idx}) out of the range of definitions (size {len})"
  | .outOfContextRange name idx len => s!"'{name}' (index {idx}) out of context range (size {len})"
  | .impossibleEqualCase => "Impossible equal case"
  | .impossibleProjectionCase => "Impossible case on projections"
  | .impossibleEvalCase => "Impossible eval case"
  | .impossible => "Impossible case. Implementation broken."
  | .cannotEvalQuotient => "Cannot evaluate this quotient"
  | .unknownConst => "Unknown constant name"
  | .noName => "No way to extract a name"
  | .custom str => str

end Yatima.Typechecker
