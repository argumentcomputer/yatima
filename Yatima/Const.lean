import Yatima.Name
import Yatima.Expr

namespace Yatima

structure Axiom where
  name: Name
  lvls: List Name
  type: Expr
  safe: Bool

structure AxiomAnon where
  lvls: Nat
  type: ExprAnonCid
  safe: Bool

structure AxiomMeta where
  name: Name
  lvls: List Name
  type: ExprMetaCid

structure Theorem where
  name: Name
  lvls: List Name
  type: Expr
  value: Expr

structure TheoremAnon where
  lvls: Nat
  type: ExprAnonCid
  value: ExprAnonCid

structure TheoremMeta where
  name: Name
  lvls: List Name
  type: ExprMetaCid
  value: ExprMetaCid

structure Opaque where
  name: Name
  lvls: List Name
  type: Expr
  value: Expr
  safe: Bool

structure OpaqueAnon where
  lvls: Nat
  type: ExprAnonCid
  value: ExprAnonCid
  safe: Bool

structure OpaqueMeta where
  name: Name
  lvls: List Name
  type: ExprMetaCid
  value: ExprMetaCid

inductive DefSafety where
| _safe
| _unsafe
| _partial

structure Definition where
  name: Name
  lvls: List Name
  type: Expr
  value: Expr
  safe: DefSafety

structure DefinitionAnon where
  lvls: Nat
  type: ExprAnonCid
  value: ExprAnonCid
  safe: DefSafety

structure DefinitionMeta where
  name: Name
  lvls: List Name
  type: ExprMetaCid
  value: ExprMetaCid

structure Inductive where
  name: Name
  lvls: List Name
  type: Expr
  params: Nat
  indices: Nat
  ctors: List Name
  recr: Bool
  safe: Bool
  refl: Bool
  nest: Bool

structure InductiveAnon where
  lvls: Nat
  type: ExprAnonCid
  params: Nat
  indices: Nat
  ctors: Nat
  recr: Bool
  safe: Bool
  refl: Bool
  nest: Bool

structure InductiveMeta where
  name: Name
  lvls: List Name
  type: ExprMetaCid
  ctors: List Name

structure Constructor where
  name: Name
  lvls: List Name
  type: Expr
  ind: ConstCid
  idx: Nat
  params: Nat
  fields: Nat
  safe: Bool

structure ConstructorAnon where
  lvls: Nat
  type: ExprAnonCid
  ind: ConstAnonCid
  idx: Nat
  params: Nat
  fields: Nat
  safe: Bool

structure ConstructorMeta where
  name: Name
  lvls: List Name
  type: ExprMetaCid
  ind: ConstMetaCid

structure RecRule where
  ctor : ConstCid
  fields: Nat
  rhs: Expr

structure RecRuleAnon where
  ctor : ConstAnonCid
  fields: Nat
  rhs: ExprAnonCid

structure RecRuleMeta where
  ctor : ConstMetaCid
  rhs: ExprMetaCid

structure Recursor where
  name: Name
  lvls: List Name
  type: Expr
  ind: ConstCid
  params: Nat
  indices: Nat
  motives: Nat
  minors: Nat
  rules : List RecRule
  k: Bool
  safe: Bool

structure RecursorAnon where
  lvls: Nat
  type: ExprAnonCid
  ind: ConstAnonCid
  params: Nat
  indices: Nat
  motives: Nat
  minors: Nat
  rules : List RecRuleAnon
  k: Bool
  safe: Bool

structure RecursorMeta where
  name: Name
  lvls: List Name
  type: ExprMetaCid
  ind: ConstMetaCid
  rules : List RecRuleMeta

inductive QuotKind where
| type
| ctor
| lift
| ind

structure Quotient where
  name: Name
  lvls: List Name
  type: Expr
  kind: QuotKind

structure QuotientAnon where
  lvls: Nat
  type: ExprAnonCid
  kind: QuotKind

structure QuotientMeta where
  name: Name
  lvls: List Name
  type: ExprMetaCid

inductive Const
| «axiom» : Axiom → Const
| «theorem» : Theorem → Const
| «inductive» : Inductive → Const
| opaque : Opaque → Const
| definition : Definition → Const
| constructor : Constructor → Const
| recursor : Recursor → Const
| quotient : Quotient → Const

inductive ConstAnon
| «axiom» : AxiomAnon → ConstAnon
| «theorem» : TheoremAnon → ConstAnon
| «inductive» : InductiveAnon → ConstAnon
| opaque : OpaqueAnon → ConstAnon
| definition : DefinitionAnon → ConstAnon
| constructor : ConstructorAnon → ConstAnon
| recursor : RecursorAnon → ConstAnon
| quotient : QuotientAnon → ConstAnon

inductive ConstMeta
| «axiom» : AxiomMeta → ConstMeta
| «theorem» : TheoremMeta → ConstMeta
| «inductive» : InductiveMeta → ConstMeta
| opaque : OpaqueMeta → ConstMeta
| definition : DefinitionMeta → ConstMeta
| constructor : ConstructorMeta → ConstMeta
| recursor : RecursorMeta → ConstMeta
| quotient : QuotientMeta → ConstMeta

end Yatima
