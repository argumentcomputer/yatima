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
  expr: Expr

structure TheoremAnon where
  lvls: Nat
  type: ExprAnonCid
  expr: ExprAnonCid

structure TheoremMeta where
  name: Name
  lvls: List Name
  type: ExprMetaCid
  expr: ExprMetaCid

structure Opaque where
  name: Name
  lvls: List Name
  type: Expr
  expr: Expr
  safe: Bool

structure OpaqueAnon where
  lvls: Nat
  type: ExprAnonCid
  expr: ExprAnonCid
  safe: Bool

structure OpaqueMeta where
  name: Name
  lvls: List Name
  type: ExprMetaCid
  expr: ExprMetaCid

inductive DefSafety where
| _safe
| _unsafe
| _partial

structure Definition where
  name: Name
  lvls: List Name
  type: Expr
  expr: Expr
  safe: DefSafety

structure DefinitionAnon where
  lvls: Nat
  type: ExprAnonCid
  expr: ExprAnonCid
  safe: DefSafety

structure DefinitionMeta where
  name: Name
  lvls: List Name
  type: ExprMetaCid
  expr: ExprMetaCid

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
| _axiom : Axiom → Const
| _theorem : Theorem → Const
| _opaque : Opaque → Const
| _definition : Definition → Const
| _inductitve : Inductive → Const
| _constructor : Constructor → Const
| _recursor : Recursor → Const
| _quotient : Quotient → Const

inductive ConstAnon
| _axiom : AxiomAnon → ConstAnon
| _theorem : TheoremAnon → ConstAnon
| _opaque : OpaqueAnon → ConstAnon
| _definition : DefinitionAnon → ConstAnon
| _inductitve : InductiveAnon → ConstAnon
| _constructor : ConstructorAnon → ConstAnon
| _recursor : RecursorAnon → ConstAnon
| _quotient : QuotientAnon → ConstAnon

inductive ConstMeta
| _axiom : AxiomMeta → ConstMeta
| _theorem : TheoremMeta → ConstMeta
| _opaque : OpaqueMeta → ConstMeta
| _definition : DefinitionMeta → ConstMeta
| _inductitve : InductiveMeta → ConstMeta
| _constructor : ConstructorMeta → ConstMeta
| _recursor : RecursorMeta → ConstMeta
| _quotient : QuotientMeta → ConstMeta

end Yatima
