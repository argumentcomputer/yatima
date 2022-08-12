import Yatima.Datatypes.Expr

namespace Yatima

inductive RecType where
  | intr : RecType
  | extr : RecType
  deriving BEq, Inhabited

instance : Coe RecType Bool where coe | .intr => .true | .extr => .false
def Split.intr : A → Split A B RecType.intr := Split.inj₁
def Split.extr : B → Split A B RecType.extr := Split.inj₂

inductive DefinitionSafety where
  | safe | «unsafe» | «partial» deriving BEq, Inhabited, Repr

inductive QuotKind where
  | type | ctor | lift | ind deriving BEq

namespace Ipld

abbrev NatₗListNameᵣ := Split Nat (List Name)

abbrev Boolₗ := Split Bool Unit

structure Axiom (k : Kind) where
  name : Nameᵣ k
  lvls : NatₗListNameᵣ k
  type : ExprCid k
  safe : Boolₗ k
  deriving Repr

structure Theorem (k : Kind) where
  name  : Nameᵣ k
  lvls  : NatₗListNameᵣ k
  type  : ExprCid k
  value : ExprCid k
  deriving Repr

structure Opaque (k : Kind) where
  name  : Nameᵣ k
  lvls  : NatₗListNameᵣ k
  type  : ExprCid k
  value : ExprCid k
  safe  : Boolₗ k
  deriving Repr

structure Definition (k : Kind) where
  name   : Nameᵣ k
  lvls   : NatₗListNameᵣ k
  type   : ExprCid k
  value  : ExprCid k
  safety : Split DefinitionSafety Unit k
  deriving Inhabited

structure DefinitionProj (k : Kind) where
  name  : Nameᵣ k
  lvls  : NatₗListNameᵣ k
  type  : ExprCid k
  block : ConstCid k
  idx   : Nat
  deriving Repr

structure Constructor (k : Kind) where
  name   : Nameᵣ k
  lvls   : NatₗListNameᵣ k
  type   : ExprCid k
  idx    : LNat k
  params : LNat k
  fields : LNat k
  rhs    : ExprCid k
  safe   : Boolₗ k
  deriving Repr

structure RecursorRule (k : Kind) where
  ctor   : ConstCid k
  fields : LNat k
  rhs    : ExprCid k
  deriving Repr

structure Recursor (b : RecType) (k : Kind) where
  name    : Nameᵣ k
  lvls    : NatₗListNameᵣ k
  type    : ExprCid k
  params  : LNat k
  indices : LNat k
  motives : LNat k
  minors  : LNat k
  rules   : Split Unit (List (RecursorRule k)) b
  k       : Boolₗ k
  deriving Repr

structure Inductive (k : Kind) where
  name     : Nameᵣ k
  lvls     : NatₗListNameᵣ k
  type     : ExprCid k
  params   : LNat k
  indices  : LNat k
  ctors    : List (Constructor k)
  recrs    : List (Sigma (Recursor · k))
  recr     : Boolₗ k
  safe     : Boolₗ k
  refl     : Boolₗ k
  deriving Inhabited

instance {k : Kind} : Repr (Inductive k) where
  reprPrec a n := reprPrec a.name n

structure InductiveProj (k : Kind) where
  name    : Nameᵣ k
  lvls    : NatₗListNameᵣ k
  type    : ExprCid k
  block   : ConstCid k
  idx     : LNat k
  deriving Repr

structure ConstructorProj (k : Kind) where
  name    : Nameᵣ k
  lvls    : NatₗListNameᵣ k
  type    : ExprCid k
  block   : ConstCid k
  idx     : LNat k
  cidx    : LNat k
  deriving Repr

structure RecursorProj (k : Kind) where
  name    : Nameᵣ k
  lvls    : NatₗListNameᵣ k
  type    : ExprCid k
  block   : ConstCid k
  idx     : LNat k
  ridx    : LNat k
  deriving Repr

structure Quotient (k : Kind) where
  name : Nameᵣ k
  lvls : NatₗListNameᵣ k
  type : ExprCid k
  kind : Split QuotKind Unit k

instance {k : Kind} : Repr (Quotient k) where
  reprPrec a n := reprPrec a.name n

inductive Const (k : Kind) where
  -- standalone constants
  | «axiom»     : Axiom k → Const k
  | «theorem»   : Theorem k → Const k
  | «opaque»    : Opaque k → Const k
  | quotient    : Quotient k → Const k
  -- projections of mutual blocks
  | inductiveProj   : InductiveProj k → Const k
  | constructorProj : ConstructorProj k → Const k
  | recursorProj    : RecursorProj k → Const k
  | definitionProj  : DefinitionProj k → Const k
  -- constants to represent mutual blocks
  | mutDefBlock : List (Split (Definition k) (List (Definition k)) k) → Const k
  | mutIndBlock : List (Inductive k) → Const k

def Const.ctorName : Ipld.Const k → String
  | .axiom           _ => "axiom"
  | .theorem         _ => "theorem"
  | .opaque          _ => "opaque"
  | .quotient        _ => "quotient"
  | .definitionProj  _ => "definition projection"
  | .inductiveProj   _ => "inductive projection"
  | .constructorProj _ => "constructor projection"
  | .recursorProj    _ => "recursor projection"
  | .mutDefBlock     _ => "mutual definition block"
  | .mutIndBlock     _ => "mutual inductive block"

def Const.name : Ipld.Const .meta → Name
  | .axiom           x 
  | .theorem         x 
  | .opaque          x 
  | .quotient        x 
  | .definitionProj  x 
  | .inductiveProj   x 
  | .constructorProj x 
  | .recursorProj    x => x.name.proj₂
  | .mutDefBlock     _
  | .mutIndBlock     _ => .anonymous

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

def Const.name : Const → Name
  | .axiom       x
  | .theorem     x
  | .opaque      x
  | .inductive   x
  | .definition  x
  | .constructor x
  | .extRecursor x
  | .intRecursor x
  | .quotient    x => x.name

def Const.type : Const → Expr
  | .axiom       x
  | .theorem     x
  | .inductive   x
  | .opaque      x
  | .definition  x
  | .constructor x
  | .intRecursor x
  | .extRecursor x
  | .quotient    x => x.type

def Const.ctorName : Const → String
  | .axiom       _ => "axiom"
  | .theorem     _ => "theorem"
  | .opaque      _ => "opaque"
  | .definition  _ => "definition"
  | .inductive   _ => "inductive"
  | .constructor _ => "constructor"
  | .extRecursor _ => "external recursor"
  | .intRecursor _ => "internal recursor"
  | .quotient    _ => "quotient"

end Yatima
