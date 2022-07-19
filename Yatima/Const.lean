import Yatima.Expr

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

structure Recursor (k : Kind) (b : RecType) where
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
  recrs    : List (Sigma (Recursor k))
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

structure Axiom (Expr : Type) where
  name : Name
  lvls : List Name
  type : Expr
  safe : Bool
  deriving Inhabited

structure Theorem (Expr : Type) where
  name  : Name
  lvls  : List Name
  type  : Expr
  value : Expr

structure Opaque (Expr : Type) where
  name  : Name
  lvls  : List Name
  type  : Expr
  value : Expr
  safe  : Bool

structure Definition (Expr : Type) where
  name   : Name
  lvls   : List Name
  type   : Expr
  value  : Expr
  safety : DefinitionSafety

structure Constructor where
  name   : Name
  lvls   : List Name
  type   : Expr
  idx    : Nat
  params : Nat
  fields : Nat
  rhs    : Expr
  safe   : Bool

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

structure RecursorRule where
  ctor   : Constructor
  fields : Nat
  rhs    : Expr

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

structure IntRecursor where
  name    : Name
  lvls    : List Name
  type    : Expr
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  k       : Bool

structure Quotient (Expr : Type) where
  name : Name
  lvls : List Name
  type : Expr
  kind : QuotKind

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
  deriving Inhabited

def Opaque.toIpld {k : Ipld.Kind} (d : Opaque) (typeCid valueCid: ExprCid) : Ipld.Opaque k :=
match k with
  | .Anon => ⟨(), d.lvls.length, typeCid.anon, valueCid.anon, d.safe⟩
  | .Meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta, ()⟩

def Quotient.toIpld {k : Ipld.Kind} (d : Quotient) (typeCid : ExprCid) : Ipld.Quotient k :=
match k with
  | .Anon => ⟨(), d.lvls.length, typeCid.anon, d.kind⟩
  | .Meta => ⟨d.name, d.lvls, typeCid.meta, ()⟩

def Axiom.toIpld {k : Ipld.Kind} (d : Axiom) (typeCid : ExprCid) : Ipld.Axiom k :=
match k with
  | .Anon => ⟨(), d.lvls.length, typeCid.anon, d.safe⟩
  | .Meta => ⟨d.name, d.lvls, typeCid.meta, ()⟩

def Theorem.toIpld {k : Ipld.Kind} (d : Theorem) (typeCid valueCid : ExprCid) : Ipld.Theorem k :=
match k with
  | .Anon => ⟨(), d.lvls.length, typeCid.anon, valueCid.anon⟩
  | .Meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta⟩

def Definition.toIpld {k : Ipld.Kind} (d : Definition) (typeCid valueCid : ExprCid) : Ipld.Definition k :=
match k with
  | .Anon => ⟨(), d.lvls.length, typeCid.anon, valueCid.anon, d.safety⟩
  | .Meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta, ()⟩

def Constructor.toIpld {k : Ipld.Kind} (c : Constructor) (typeCid rhsCid : ExprCid) : Ipld.Constructor k :=
match k with
  | .Anon => ⟨(), c.lvls.length, typeCid.anon, c.idx, c.params, c.fields, rhsCid.anon, c.safe⟩
  | .Meta => ⟨c.name, c.lvls, typeCid.meta, (), (), (), rhsCid.meta, ()⟩

def RecursorRule.toIpld {k : Ipld.Kind} (r : RecursorRule) (ctorCid : ConstCid) (rhsCid : ExprCid) : Ipld.RecursorRule k :=
match k with
  | .Anon => ⟨ctorCid.anon, r.fields, rhsCid.anon⟩
  | .Meta => ⟨ctorCid.meta, (), rhsCid.meta⟩

def ExtRecursor.toIpld {k : Ipld.Kind} (r : ExtRecursor) (typeCid : ExprCid) (rulesCids : List $ Ipld.RecursorRule k) : Ipld.Recursor k .Extr :=
match k with
  | .Anon =>
    ⟨ ()
    , r.lvls.length
    , typeCid.anon
    , r.params
    , r.indices
    , r.motives
    , r.minors
    , rulesCids
    --, .inj₂ $ r.rules.enum.map $ fun (i, rule) => rule.toIpld rulesCids[i]!.1 rulesCids[i]!.2
    , r.k ⟩
  | .Meta =>
    ⟨ r.name
    , r.lvls
    , typeCid.meta
    , (), (), (), ()
    , rulesCids
    , ()⟩

def IntRecursor.toIpld {k : Ipld.Kind} (r : IntRecursor) (typeCid : ExprCid) : Ipld.Recursor k .Intr :=
match k with
  | .Anon =>
    ⟨ ()
    , r.lvls.length
    , typeCid.anon
    , r.params
    , r.indices
    , r.motives
    , r.minors
    , .inj₁ ()
    , r.k ⟩
  | .Meta =>
    ⟨ r.name
    , r.lvls
    , typeCid.meta
    , (), (), (), ()
    , .inj₁ ()
    , ()⟩

def Inductive.toIpld {k : Ipld.Kind} (i : Inductive) (idx : Nat) (typeCid : ExprCid) (blockCid : ConstCid) : Ipld.InductiveProj k :=
match k with
  | .Anon =>
    ⟨ ()
    , i.lvls.length
    , typeCid.anon
    , blockCid.anon
    , idx ⟩
  | .Meta =>
    ⟨ i.name
    , i.lvls
    , typeCid.meta
    , blockCid.meta
    , () ⟩

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
