import Yatima.Datatypes.Expr

namespace Yatima

inductive RecType where
| Intr : RecType
| Extr : RecType
deriving BEq, Inhabited

instance : Coe RecType Bool where coe | .Intr => .true | .Extr => .false
def Split.intr : A → Split A B RecType.Intr := Split.inj₁
def Split.extr : B → Split A B RecType.Extr := Split.inj₂

inductive DefinitionSafety where
  | safe | «unsafe» | «partial» deriving BEq

inductive QuotKind where
  | type | ctor | lift | ind deriving BEq

namespace Ipld

abbrev ListName? := Split Nat (List Name)
abbrev Bool? := Split Bool Unit

structure Axiom (k : Kind) where
  name : Name? k
  lvls : ListName? k
  type : ExprCid k
  safe : Bool? k

structure Theorem (k : Kind) where
  name  : Name? k
  lvls  : ListName? k
  type  : ExprCid k
  value : ExprCid k

structure Opaque (k : Kind) where
  name  : Name? k
  lvls  : ListName? k
  type  : ExprCid k
  value : ExprCid k
  safe  : Bool? k

structure Definition (k : Kind) where
  name   : Name? k
  lvls   : ListName? k
  type   : ExprCid k
  value  : ExprCid k
  safety : Split DefinitionSafety Unit k

structure DefinitionProj (k : Kind) where
  name  : Name? k
  lvls  : ListName? k
  type  : ExprCid k
  block : ConstCid k
  idx   : Nat? k

structure Constructor (k : Kind) where
  name   : Name? k
  lvls   : ListName? k
  type   : ExprCid k
  idx    : Nat? k
  params : Nat? k
  fields : Nat? k
  rhs    : ExprCid k
  safe   : Bool? k

structure RecursorRule (k : Kind) where
  ctor   : ConstCid k
  fields : Nat? k
  rhs    : ExprCid k

structure Recursor (b : RecType) (k : Kind) where
  name    : Name? k
  lvls    : ListName? k
  type    : ExprCid k
  params  : Nat? k
  indices : Nat? k
  motives : Nat? k
  minors  : Nat? k
  rules   : Split Unit (List (RecursorRule k)) b
  k       : Bool? k

structure Inductive (k : Kind) where
  name     : Name? k
  lvls     : ListName? k
  type     : ExprCid k
  params   : Nat? k
  indices  : Nat? k
  ctors    : List (Constructor k)
  recrs    : List (Sigma (Recursor · k))
  recr     : Bool? k
  safe     : Bool? k
  refl     : Bool? k
  deriving Inhabited

structure InductiveProj (k : Kind) where
  name    : Name? k
  lvls    : ListName? k
  type    : ExprCid k
  block   : ConstCid k
  idx     : Nat? k

structure ConstructorProj (k : Kind) where
  name    : Name? k
  lvls    : ListName? k
  type    : ExprCid k
  block   : ConstCid k
  idx     : Nat? k
  cidx    : Nat? k

structure RecursorProj (k : Kind) where
  name    : Name? k
  lvls    : ListName? k
  type    : ExprCid k
  block   : ConstCid k
  idx     : Nat? k
  ridx    : Nat? k

structure Quotient (k : Kind) where
  name : Name? k
  lvls : ListName? k
  type : ExprCid k
  kind : Split QuotKind Unit k

inductive Const (k : Kind) where
  -- standalone constants
  | «axiom»     : Axiom k → Const k
  | «theorem»   : Theorem k → Const k
  | «opaque»    : Opaque k → Const k
  | quotient    : Quotient k → Const k
  | definition  : Definition k → Const k
  -- projections of mutual blocks
  | inductiveProj   : InductiveProj k → Const k
  | constructorProj : ConstructorProj k → Const k
  | recursorProj    : RecursorProj k → Const k
  | definitionProj  : DefinitionProj k → Const k
  -- constants to represent mutual blocks
  | mutDefBlock : List (Split (Definition k) (List (Definition k)) k) → Const k
  | mutIndBlock : List (Inductive k) → Const k
end Ipld

structure Axiom where
  name : Name
  lvls : List Name
  type : Expr
  safe : Bool
  deriving Inhabited, BEq

structure Theorem where
  name  : Name
  lvls  : List Name
  type  : Expr
  value : Expr
  deriving BEq

structure Opaque where
  name  : Name
  lvls  : List Name
  type  : Expr
  value : Expr
  safe  : Bool
  deriving BEq

structure Definition where
  name   : Name
  lvls   : List Name
  type   : Expr
  value  : Expr
  safety : DefinitionSafety
  deriving BEq

structure Constructor where
  name   : Name
  lvls   : List Name
  type   : Expr
  idx    : Nat
  params : Nat
  fields : Nat
  rhs    : Expr
  safe   : Bool
  deriving BEq

structure Inductive where
  name    : Name
  lvls    : List Name
  type    : Expr
  params  : Nat
  indices : Nat
  recr    : Bool
  safe    : Bool
  refl    : Bool
  unit    : Bool
  struct  : Option Constructor
  deriving BEq

structure RecursorRule where
  ctor   : Constructor
  fields : Nat
  rhs    : Expr
  deriving BEq

structure ExtRecursor where
  name    : Name
  lvls    : List Name
  type    : Expr
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : List RecursorRule
  k       : Bool
  deriving BEq

structure IntRecursor where
  name    : Name
  lvls    : List Name
  type    : Expr
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  k       : Bool
  deriving BEq

structure Quotient where
  name : Name
  lvls : List Name
  type : Expr
  kind : QuotKind
  deriving BEq

inductive Const
  | «axiom»     : Axiom → Const
  | «theorem»   : Theorem → Const
  | «inductive» : Inductive → Const
  | «opaque»    : Opaque → Const
  | definition  : Definition → Const
  | constructor : Constructor → Const
  | extRecursor : ExtRecursor → Const
  | intRecursor : IntRecursor → Const
  | quotient    : Quotient → Const
  deriving Inhabited, BEq

def Const.type (k : Const) : Expr :=
  match k with
  | .axiom x => x.type
  | .theorem x => x.type
  | .inductive x => x.type
  | .opaque x => x.type
  | .definition x => x.type
  | .constructor x => x.type
  | .intRecursor x => x.type
  | .extRecursor x => x.type
  | .quotient x => x.type

def Const.name : Const → Name
  | .axiom           x
  | .theorem         x
  | .opaque          x
  | .inductive       x
  | .definition      x
  | .constructor     x
  | .extRecursor     x
  | .intRecursor     x
  | .quotient        x => x.name

def Const.ctorName : Const → String
  | .axiom           _ => "axiom"
  | .theorem         _ => "theorem"
  | .opaque          _ => "opaque"
  | .definition      _ => "definition"
  | .inductive       _ => "inductive"
  | .constructor     _ => "constructor"
  | .extRecursor     _ => "external recursor"
  | .intRecursor     _ => "internal recursor"
  | .quotient        _ => "quotient"

end Yatima
