import Yatima.Datatypes.Expr

namespace Yatima

namespace IR

structure AxiomAnon where
  lvls : Nat
  type : Hash
  safe : Bool
  deriving Ord, BEq

structure AxiomMeta where
  name : Name
  lvls : List Name
  type : Hash
  deriving Ord, BEq

structure TheoremAnon where
  lvls  : Nat
  type  : Hash
  value : Hash
  deriving Ord, BEq

structure TheoremMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  value : Hash
  deriving Ord, BEq

structure OpaqueAnon where
  lvls  : Nat
  type  : Hash
  value : Hash
  safe  : Bool
  deriving Ord, BEq

structure OpaqueMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  value : Hash
  deriving Ord, BEq

structure QuotientAnon where
  lvls : Nat
  type : Hash
  kind : QuotKind
  deriving Ord, BEq

structure QuotientMeta where
  name : Name
  lvls : List Name
  type : Hash
  deriving Ord, BEq

structure DefinitionAnon where
  lvls   : Nat
  type   : Hash
  value  : Hash
  safety : DefinitionSafety
  deriving Inhabited, Ord, BEq

structure DefinitionMeta where
  name   : Name
  lvls   : List Name
  type   : Hash
  value  : Hash
  deriving Inhabited, Ord, BEq

structure DefinitionProjAnon where
  lvls  : Nat
  type  : Hash
  block : Hash
  idx   : Nat
  deriving Ord, BEq

structure DefinitionProjMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  block : Hash
  idx   : Nat
  deriving Ord, BEq

structure ConstructorAnon where
  lvls   : Nat
  type   : Hash
  idx    : Nat
  params : Nat
  fields : Nat
  safe   : Bool
  deriving Ord, BEq

structure ConstructorMeta where
  name   : Name
  lvls   : List Name
  type   : Hash
  deriving Ord, BEq

structure RecursorRuleAnon where
  fields : Nat
  rhs    : Hash
  deriving Ord, BEq

structure RecursorRuleMeta where
  rhs : Hash
  deriving Ord, BEq

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
  deriving Ord, BEq

structure RecursorMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  rules : List RecursorRuleMeta
  deriving Ord, BEq

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
  deriving Inhabited, Ord, BEq

structure InductiveMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  ctors : List ConstructorMeta
  recrs : List RecursorMeta
  deriving Inhabited, Ord, BEq

structure InductiveProjAnon where
  lvls  : Nat
  type  : Hash
  block : Hash
  idx   : Nat
  deriving Ord, BEq

structure InductiveProjMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  block : Hash
  deriving Ord, BEq

structure ConstructorProjAnon where
  lvls  : Nat
  type  : Hash
  block : Hash
  idx   : Nat
  cidx  : Nat
  deriving Ord, BEq

structure ConstructorProjMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  block : Hash
  deriving Ord, BEq

structure RecursorProjAnon where
  lvls  : Nat
  type  : Hash
  block : Hash
  idx   : Nat
  ridx  : Nat
  deriving Ord, BEq

structure RecursorProjMeta where
  name  : Name
  lvls  : List Name
  type  : Hash
  block : Hash
  deriving Ord, BEq

inductive ConstAnon where
  -- standalone constants
  | «axiom»   : AxiomAnon    → ConstAnon
  | «theorem» : TheoremAnon  → ConstAnon
  | «opaque»  : OpaqueAnon   → ConstAnon
  | quotient  : QuotientAnon → ConstAnon
  -- projections of mutual blocks
  | inductiveProj   : InductiveProjAnon   → ConstAnon
  | constructorProj : ConstructorProjAnon → ConstAnon
  | recursorProj    : RecursorProjAnon    → ConstAnon
  | definitionProj  : DefinitionProjAnon  → ConstAnon
  -- constants to represent mutual blocks
  | mutDefBlock : List DefinitionAnon → ConstAnon
  | mutIndBlock : List InductiveAnon  → ConstAnon
  deriving Ord, BEq

inductive ConstMeta where
  -- standalone constants
  | «axiom»   : AxiomMeta    → ConstMeta
  | «theorem» : TheoremMeta  → ConstMeta
  | «opaque»  : OpaqueMeta   → ConstMeta
  | quotient  : QuotientMeta → ConstMeta
  -- projections of mutual blocks
  | inductiveProj   : InductiveProjMeta   → ConstMeta
  | constructorProj : ConstructorProjMeta → ConstMeta
  | recursorProj    : RecursorProjMeta    → ConstMeta
  | definitionProj  : DefinitionProjMeta  → ConstMeta
  -- constants to represent mutual blocks
  | mutDefBlock : List (List DefinitionMeta) → ConstMeta
  | mutIndBlock : List InductiveMeta  → ConstMeta
  deriving Ord, BEq

end IR

namespace TC

open Lurk (F)

structure Axiom where
  lvls : Nat
  type : Expr
  safe : Bool
  deriving Ord, BEq

structure Theorem where
  lvls  : Nat
  type  : Expr
  value : Expr
  deriving Ord, BEq

structure Opaque where
  lvls  : Nat
  type  : Expr
  value : Expr
  safe  : Bool
  deriving Ord, BEq

structure Quotient where
  lvls : Nat
  type : Expr
  kind : QuotKind
  deriving Ord, BEq

structure Definition where
  lvls   : Nat
  type   : Expr
  value  : Expr
  safety : DefinitionSafety
  -- all of the mutual definitions in this block; needed to prevent infinite loops while typechecking
  all    : List F
  deriving Inhabited, Ord, BEq

structure Constructor where
  lvls   : Nat
  type   : Expr
  idx    : Nat
  params : Nat
  fields : Nat
  safe   : Bool
  deriving Ord, BEq

structure RecursorRule where
  fields : Nat
  rhs    : Expr
  deriving Ord, BEq

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
  -- needed for eta-expansion of structs
  ind      : F
  -- all of the recursors related to this inductive; needed to prevent infinite loops while typechecking
  all      : List F
  deriving Ord, BEq

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
  -- needed for eta-expansion of structs
  struct  : Option F
  -- needed for unit-like equality
  unit    : Bool
  deriving Inhabited, Ord, BEq

inductive Const where
  -- standalone constants
  | «axiom»     : Axiom    → Const
  | «theorem»   : Theorem  → Const
  | «opaque»    : Opaque   → Const
  | quotient    : Quotient → Const
  | «inductive» : Inductive → Const
  | constructor : Constructor → Const
  | recursor    : Recursor → Const
  | definition  : Definition → Const
  deriving Ord, BEq

namespace Const

def levels : Const → Nat
  | .axiom       x
  | .theorem     x
  | .inductive   x
  | .opaque      x
  | .definition  x
  | .constructor x
  | .recursor    x
  | .quotient    x => x.lvls

def type : Const → Expr
  | .axiom       x
  | .theorem     x
  | .inductive   x
  | .opaque      x
  | .definition  x
  | .constructor x
  | .recursor    x
  | .quotient    x => x.type

end Const

end TC

end Yatima
