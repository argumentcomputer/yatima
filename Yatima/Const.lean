import Yatima.Name
import Yatima.Expr

namespace Yatima

structure Axiom where
  name : Name
  lvls : List Name
  type : ExprCid
  safe : Bool

structure AxiomAnon where
  lvls : Nat
  type : ExprAnonCid
  safe : Bool

structure AxiomMeta where
  name : Name
  lvls : List Name
  type : ExprMetaCid

structure Theorem where
  name  : Name
  lvls  : List Name
  type  : ExprCid
  value : ExprCid

structure TheoremAnon where
  lvls  : Nat
  type  : ExprAnonCid
  value : ExprAnonCid

structure TheoremMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  value : ExprMetaCid

structure Opaque where
  name  : Name
  lvls  : List Name
  type  : ExprCid
  value : ExprCid
  safe  : Bool

structure OpaqueAnon where
  lvls  : Nat
  type  : ExprAnonCid
  value : ExprAnonCid
  safe  : Bool

structure OpaqueMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  value : ExprMetaCid

inductive DefinitionSafety where
  | safe | «unsafe» | «partial»

structure Definition where
  name   : Name
  lvls   : List Name
  type   : ExprCid
  value  : ExprCid
  safety : DefinitionSafety

structure DefinitionAnon where
  lvls   : Nat
  type   : ExprAnonCid
  value  : ExprAnonCid
  safety : DefinitionSafety

structure DefinitionMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  value : ExprMetaCid

structure Inductive where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  params  : Nat
  indices : Nat
  ctors   : List Name
  recr    : Bool
  safe    : Bool
  refl    : Bool
  nest    : Bool

structure InductiveAnon where
  lvls    : Nat
  type    : ExprAnonCid
  params  : Nat
  indices : Nat
  ctors   : Nat
  recr    : Bool
  safe    : Bool
  refl    : Bool
  nest    : Bool

structure InductiveMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  ctors : List Name

structure Constructor where
  name   : Name
  lvls   : List Name
  type   : ExprCid
  ind    : ConstCid
  idx    : Nat
  params : Nat
  fields : Nat
  safe   : Bool

structure ConstructorAnon where
  lvls   : Nat
  type   : ExprAnonCid
  ind    : ConstAnonCid
  idx    : Nat
  params : Nat
  fields : Nat
  safe   : Bool

structure ConstructorMeta where
  name : Name
  lvls : List Name
  type : ExprMetaCid
  ind  : ConstMetaCid

structure RecursorRule where
  ctor   : ConstCid
  fields : Nat
  rhs    : ExprCid

structure RecursorRuleAnon where
  ctor   : ConstAnonCid
  fields : Nat
  rhs    : ExprAnonCid

structure RecursorRuleMeta where
  ctor : ConstMetaCid
  rhs  : ExprMetaCid

structure Recursor where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  ind     : ConstCid
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : List RecursorRule
  k       : Bool
  safe    : Bool

structure RecursorAnon where
  lvls    : Nat
  type    : ExprAnonCid
  ind     : ConstAnonCid
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : List RecursorRuleAnon
  k       : Bool
  safe    : Bool

structure RecursorMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  ind   : ConstMetaCid
  rules : List RecursorRuleMeta

inductive QuotKind where
  | type | ctor | lift | ind

structure Quotient where
  name : Name
  lvls : List Name
  type : ExprCid
  kind : QuotKind

structure QuotientAnon where
  lvls : Nat
  type : ExprAnonCid
  kind : QuotKind

structure QuotientMeta where
  name : Name
  lvls : List Name
  type : ExprMetaCid

inductive Const
  | «axiom»     : Axiom → Const
  | «theorem»   : Theorem → Const
  | «inductive» : Inductive → Const
  | opaque      : Opaque → Const
  | definition  : Definition → Const
  | constructor : Constructor → Const
  | recursor    : Recursor → Const
  | quotient    : Quotient → Const

inductive ConstAnon
| «axiom»     : AxiomAnon → ConstAnon
| «theorem»   : TheoremAnon → ConstAnon
| «inductive» : InductiveAnon → ConstAnon
| opaque      : OpaqueAnon → ConstAnon
| definition  : DefinitionAnon → ConstAnon
| constructor : ConstructorAnon → ConstAnon
| recursor    : RecursorAnon → ConstAnon
| quotient    : QuotientAnon → ConstAnon

inductive ConstMeta
  | «axiom»     : AxiomMeta → ConstMeta
  | «theorem»   : TheoremMeta → ConstMeta
  | «inductive» : InductiveMeta → ConstMeta
  | opaque      : OpaqueMeta → ConstMeta
  | definition  : DefinitionMeta → ConstMeta
  | constructor : ConstructorMeta → ConstMeta
  | recursor    : RecursorMeta → ConstMeta
  | quotient    : QuotientMeta → ConstMeta

end Yatima
