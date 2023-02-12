import Yatima.Datatypes.Expr

namespace Yatima

namespace IR

structure AxiomAnon where
  lvls : Nat
  type : Hash
  safe : Bool
  deriving Ord, BEq, Repr

structure AxiomMeta where
  name : Name
  lvls : List Name
  type : Hash
  deriving Ord, BEq, Repr

structure TheoremAnon where
  lvls  : Nat
  type  : Hash
  value : Hash
  deriving Ord, BEq, Repr

structure TheoremMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  value : Hash
  deriving Ord, BEq, Repr

structure OpaqueAnon where
  lvls  : Nat
  type  : Hash
  value : Hash
  safe  : Bool
  deriving Ord, BEq, Repr

structure OpaqueMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  value : Hash
  deriving Ord, BEq, Repr

deriving instance Repr for Lean.QuotKind

structure QuotientAnon where
  lvls : Nat
  type : Hash
  kind : QuotKind
  deriving Ord, BEq, Repr

structure QuotientMeta where
  name : Name
  lvls : List Name
  type : Hash
  deriving Ord, BEq, Repr

structure DefinitionAnon where
  lvls   : Nat
  type   : Hash
  value  : Hash
  safety : DefinitionSafety
  deriving Inhabited, Ord, BEq, Repr

structure DefinitionMeta where
  name   : Name
  lvls   : List Name
  type   : Hash
  value  : Hash
  deriving Inhabited, Ord, BEq, Repr

structure DefinitionProjAnon where
  block : Hash
  idx   : Nat
  deriving Ord, BEq, Repr

structure DefinitionProjMeta where
  block : Hash
  idx   : Nat
  deriving Ord, BEq, Repr

structure ConstructorAnon where
  lvls   : Nat
  type   : Hash
  idx    : Nat
  params : Nat
  fields : Nat
  safe   : Bool
  deriving Ord, BEq, Repr

structure ConstructorMeta where
  name   : Name
  lvls   : List Name
  type   : Hash
  deriving Ord, BEq, Repr

structure RecursorRuleAnon where
  fields : Nat
  rhs    : Hash
  deriving Ord, BEq, Repr

structure RecursorRuleMeta where
  rhs : Hash
  deriving Ord, BEq, Repr

structure RecursorAnon where
  lvls     : Nat
  type     : Hash
  params   : Nat
  indices  : Nat
  motives  : Nat
  minors   : Nat
  rules    : List RecursorRuleAnon
  isK      : Bool
  internal : Bool
  deriving Ord, BEq, Repr

structure RecursorMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  rules : List RecursorRuleMeta
  deriving Ord, BEq, Repr

structure InductiveAnon where
  lvls    : Nat
  type    : Hash
  params  : Nat
  indices : Nat
  ctors   : List ConstructorAnon
  recrs   : List RecursorAnon
  recr    : Bool
  safe    : Bool
  refl    : Bool
  deriving Inhabited, Ord, BEq, Repr

structure InductiveMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  ctors : List ConstructorMeta
  recrs : List RecursorMeta
  deriving Inhabited, Ord, BEq, Repr

structure InductiveProjAnon where
  block : Hash
  idx   : Nat
  deriving Ord, BEq, Repr

structure InductiveProjMeta where
  block : Hash
  idx   : Nat
  deriving Ord, BEq, Repr

structure ConstructorProjAnon where
  block : Hash
  idx   : Nat
  cidx  : Nat
  deriving Ord, BEq, Repr

structure ConstructorProjMeta where
  block : Hash
  idx   : Nat
  cidx  : Nat
  deriving Ord, BEq, Repr

structure RecursorProjAnon where
  block : Hash
  idx   : Nat
  ridx  : Nat
  deriving Ord, BEq, Repr

structure RecursorProjMeta where
  block : Hash
  idx   : Nat
  ridx  : Nat
  deriving Ord, BEq, Repr

inductive ConstAnon where
  -- standalone constants
  | «axiom»    : AxiomAnon      → ConstAnon
  | «theorem»  : TheoremAnon    → ConstAnon
  | «opaque»   : OpaqueAnon     → ConstAnon
  | definition : DefinitionAnon → ConstAnon
  | quotient   : QuotientAnon   → ConstAnon
  -- projections of mutual blocks
  | inductiveProj   : InductiveProjAnon   → ConstAnon
  | constructorProj : ConstructorProjAnon → ConstAnon
  | recursorProj    : RecursorProjAnon    → ConstAnon
  | definitionProj  : DefinitionProjAnon  → ConstAnon
  -- constants to represent mutual blocks
  | mutDefBlock : List DefinitionAnon → ConstAnon
  | mutIndBlock : List InductiveAnon  → ConstAnon
  deriving Ord, BEq, Repr

inductive ConstMeta where
  -- standalone constants
  | «axiom»    : AxiomMeta      → ConstMeta
  | «theorem»  : TheoremMeta    → ConstMeta
  | «opaque»   : OpaqueMeta     → ConstMeta
  | definition : DefinitionMeta → ConstMeta
  | quotient   : QuotientMeta   → ConstMeta
  -- projections of mutual blocks
  | inductiveProj   : InductiveProjMeta   → ConstMeta
  | constructorProj : ConstructorProjMeta → ConstMeta
  | recursorProj    : RecursorProjMeta    → ConstMeta
  | definitionProj  : DefinitionProjMeta  → ConstMeta
  -- constants to represent mutual blocks
  | mutDefBlock : List (List DefinitionMeta) → ConstMeta
  | mutIndBlock : List InductiveMeta  → ConstMeta
  deriving Ord, BEq, Repr

end IR

namespace TC

open Lurk (F)

structure Axiom where
  lvls : Nat
  type : Expr
  safe : Bool
  deriving Ord, BEq, Hashable, Repr

structure Theorem where
  lvls  : Nat
  type  : Expr
  value : Expr
  deriving Ord, BEq, Hashable, Repr

structure Opaque where
  lvls  : Nat
  type  : Expr
  value : Expr
  safe  : Bool
  deriving Ord, BEq, Hashable, Repr

structure Quotient where
  lvls : Nat
  type : Expr
  kind : QuotKind
  deriving Ord, BEq, Hashable, Repr

structure Definition where
  lvls     : Nat
  type     : Expr
  value    : Expr
  safety   : DefinitionSafety
  deriving Inhabited, Ord, BEq, Hashable, Repr

structure Constructor where
  lvls   : Nat
  type   : Expr
  idx    : Nat
  params : Nat
  fields : Nat
  safe   : Bool
  deriving Ord, BEq, Hashable, Repr

structure RecursorRule where
  fields : Nat
  rhs    : Expr
  deriving Ord, BEq, Hashable, Repr

structure Recursor where
  lvls     : Nat
  type     : Expr
  params   : Nat
  indices  : Nat
  motives  : Nat
  minors   : Nat
  rules    : List RecursorRule
  isK      : Bool
  internal : Bool
  deriving Ord, BEq, Hashable, Repr

structure Inductive where
  lvls    : Nat
  type    : Expr
  params  : Nat
  indices : Nat
  ctors   : List Constructor
  recrs   : List Recursor
  recr    : Bool
  safe    : Bool
  refl    : Bool
  struct  : Bool
  /-- whether or not this inductive is unit-like;
  needed for unit-like equality -/
  unit    : Bool
  deriving Inhabited, Ord, BEq, Hashable, Repr

structure InductiveProj where
  block : F
  idx   : Nat
  deriving Inhabited, Ord, BEq, Hashable, Repr

structure ConstructorProj where
  block : F
  idx   : Nat
  cidx  : Nat
  deriving Inhabited, Ord, BEq, Hashable, Repr

structure RecursorProj where
  block : F
  idx   : Nat
  ridx  : Nat
  deriving Inhabited, Ord, BEq, Hashable, Repr

structure DefinitionProj where
  block : F
  idx   : Nat
  deriving Inhabited, Ord, BEq, Hashable, Repr

inductive Const where
  | «axiom»     : Axiom      → Const
  | «theorem»   : Theorem    → Const
  | «opaque»    : Opaque     → Const
  | definition  : Definition → Const
  | quotient    : Quotient   → Const
  -- projections of mutual blocks
  | inductiveProj   : InductiveProj   → Const
  | constructorProj : ConstructorProj → Const
  | recursorProj    : RecursorProj    → Const
  | definitionProj  : DefinitionProj  → Const
  -- constants to represent mutual blocks
  | mutDefBlock : List Definition → Const
  | mutIndBlock : List Inductive  → Const
  deriving Ord, BEq, Hashable, Inhabited, Repr

def Const.isMutType : Const → Bool
  | .mutDefBlock _ | .mutIndBlock _ => true
  | _ => false

end TC

end Yatima
