import Yatima.Datatypes.Expr

namespace Yatima.IR

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

deriving instance Repr for Lean.QuotKind

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
  block : Lurk.F
  idx   : Nat
  deriving Inhabited, Ord, BEq, Hashable, Repr

structure ConstructorProj where
  block : Lurk.F
  idx   : Nat
  cidx  : Nat
  deriving Inhabited, Ord, BEq, Hashable, Repr

structure RecursorProj where
  block : Lurk.F
  idx   : Nat
  ridx  : Nat
  deriving Inhabited, Ord, BEq, Hashable, Repr

structure DefinitionProj where
  block : Lurk.F
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

end Yatima.IR
