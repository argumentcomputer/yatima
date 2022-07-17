import Yatima.Kind
import Yatima.Name
import Yatima.Expr

namespace Yatima

inductive RecType where
| Intr : RecType
| Extr : RecType
deriving BEq, Inhabited

instance : Coe RecType Bool where coe | .Intr => .true | .Extr => .false
def Split.intr : A → Split A B RecType.Intr := Split.fst
def Split.extr : B → Split A B RecType.Extr := Split.snd

inductive DefinitionSafety where
  | safe | «unsafe» | «partial»

inductive QuotKind where
  | type | ctor | lift | ind

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
  params : Nat? k
  fields : Nat? k
  rhs    : ExprCid k

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
  type : ExprCid
  safe : Bool

structure Theorem where
  name  : Name
  lvls  : List Name
  type  : ExprCid
  value : ExprCid

structure Opaque where
  name  : Name
  lvls  : List Name
  type  : ExprCid
  value : ExprCid
  safe  : Bool

structure Definition where
  name   : Name
  lvls   : List Name
  type   : ExprCid
  value  : ExprCid
  safety : DefinitionSafety

structure DefinitionProj where
  name  : Name
  lvls  : List Name
  type  : ExprCid
  block : ConstCid
  idx   : Nat

structure Constructor where
  name   : Name
  lvls   : List Name
  type   : ExprCid
  params : Nat
  fields : Nat
  rhs    : ExprCid

structure RecursorRule where
  ctor   : ConstCid
  fields : Nat
  rhs    : ExprCid

structure Recursor (b : RecType) where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : Split Unit (List RecursorRule) b
  k       : Bool

structure Inductive where
  name     : Name
  lvls     : List Name
  type     : ExprCid
  params   : Nat
  indices  : Nat
  ctors    : List Constructor
  recrs    : List (Sigma Recursor)
  recr     : Bool
  safe     : Bool
  refl     : Bool

structure InductiveProj where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  block   : ConstCid
  idx     : Nat

structure ConstructorProj where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  block   : ConstCid
  idx     : Nat
  cidx    : Nat

structure RecursorProj where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  block   : ConstCid
  idx     : Nat
  ridx    : Nat

structure Quotient where
  name : Name
  lvls : List Name
  type : ExprCid
  kind : QuotKind

inductive Const where
  -- standalone constants
  | «axiom»     : Axiom → Const
  | «theorem»   : Theorem → Const
  | «opaque»    : Opaque → Const
  | quotient    : Quotient → Const
  | definition  : Definition → Const
  -- projections of mutual blocks
  | inductiveProj   : InductiveProj → Const
  | constructorProj : ConstructorProj → Const
  | recursorProj    : RecursorProj → Const
  | definitionProj  : DefinitionProj → Const
  -- constants to represent mutual blocks
  | mutDefBlock : List (List (Definition)) → Const
  | mutIndBlock : List (Inductive) → Const

def Definition.to : {k : Kind} → Definition → Ipld.Definition k
  | .Anon, d => ⟨(), d.lvls.length, d.type.anon, d.value.anon, d.safety⟩
  | .Meta, d => ⟨d.name, d.lvls, d.type.meta, d.value.meta, ()⟩

def Constructor.to : {k : Kind} → Constructor → Ipld.Constructor k
  | .Anon, x => ⟨(), x.lvls.length, x.type.anon, x.params, x.fields, x.rhs.anon⟩
  | .Meta, x => ⟨x.name, x.lvls, x.type.meta, (), (), x.rhs.meta⟩

def RecursorRule.to : {k : Kind} → RecursorRule → Ipld.RecursorRule k
  | .Anon, x => ⟨x.ctor.anon, x.fields, x.rhs.anon⟩
  | .Meta, x => ⟨x.ctor.meta, (), x.rhs.meta⟩

def Recursor.to : {k : Kind} → Recursor b → Ipld.Recursor k b
  | .Anon, x =>
    ⟨ ()
    , x.lvls.length
    , x.type.anon
    , x.params
    , x.indices
    , x.motives
    , x.minors
    , match b with
      | .Intr => .intr Unit.unit
      | .Extr => .extr $ x.rules.proj₂.map $ RecursorRule.to
    , x.k ⟩
  | .Meta, x =>
    ⟨ x.name
    , x.lvls
    , x.type.meta
    , (), (), (), ()
    , match b with
      | .Intr => .intr Unit.unit
      | .Extr => .extr $ x.rules.proj₂.map $ RecursorRule.to
    , ()⟩

def Inductive.to : {k : Kind} → Inductive → Ipld.Inductive k
  | .Anon, x =>
    ⟨ ()
    , x.lvls.length
    , x.type.anon
    , x.params
    , x.indices
    , x.ctors.map (·.to)
    , x.recrs.map (fun p => .mk p.fst (Recursor.to p.snd))
    , x.recr
    , x.safe
    , x.refl ⟩
  | .Meta, x =>
    ⟨ x.name
    , x.lvls
    , x.type.meta
    , () , ()
    , x.ctors.map (·.to)
    , x.recrs.map (fun p => .mk p.fst (Recursor.to p.snd))
    , () , () , () ⟩

def Const.to : {k : Kind} → Const → Ipld.Const k
  | .Anon, .axiom a => .axiom ⟨(), a.lvls.length, a.type.anon, a.safe⟩
  | .Meta, .axiom a => .axiom ⟨a.name, a.lvls, a.type.meta, ()⟩
  | .Anon, .theorem t => .theorem ⟨(), t.lvls.length, t.type.anon, t.value.anon⟩
  | .Meta, .theorem t => .theorem ⟨t.name, t.lvls, t.type.meta, t.value.meta⟩
  | .Anon, .opaque o => .opaque ⟨(), o.lvls.length, o.type.anon, o.value.anon, o.safe⟩
  | .Meta, .opaque o => .opaque ⟨o.name, o.lvls, o.type.meta, o.value.meta, ()⟩
  | .Anon, .quotient q => .quotient ⟨(), q.lvls.length, q.type.anon, q.kind⟩
  | .Meta, .quotient q => .quotient ⟨q.name, q.lvls, q.type.meta, ()⟩
  | .Anon, .definition d => .definition d.to
  | .Meta, .definition d => .definition d.to
  | .Anon, .inductiveProj i => .inductiveProj
    ⟨ () , i.lvls.length , i.type.anon, i.block.anon, i.idx ⟩
  | .Meta, .inductiveProj i => .inductiveProj
    ⟨ i.name , i.lvls , i.type.meta, i.block.meta, () ⟩
  | .Anon, .constructorProj c => .constructorProj
    ⟨ () , c.lvls.length , c.type.anon, c.block.anon, c.idx , c.cidx ⟩
  | .Meta, .constructorProj c => .constructorProj
    ⟨ c.name , c.lvls , c.type.meta, c.block.meta, () , () ⟩
  | .Anon, .recursorProj r => .recursorProj
    ⟨ () , r.lvls.length , r.type.anon, r.block.anon, r.idx , r.ridx ⟩
  | .Meta, .recursorProj r => .recursorProj
    ⟨ r.name , r.lvls , r.type.meta, r.block.meta, () , () ⟩
  | .Anon, .definitionProj x => .definitionProj
    ⟨ () , x.lvls.length , x.type.anon, x.block.anon, x.idx ⟩
  | .Meta, .definitionProj x => .definitionProj
    ⟨ x.name , x.lvls , x.type.meta, x.block.meta, () ⟩
  | .Anon, .mutDefBlock ds => .mutDefBlock $
    (ds.map fun ds => match ds.head? with | some d => [d] | none => []).join.map (.fst ∘ Definition.to)
  | .Meta, .mutDefBlock ds => .mutDefBlock $ ds.map fun ds => .snd $ ds.map $ Definition.to
  | .Anon, .mutIndBlock is => .mutIndBlock (is.map Inductive.to)
  | .Meta, .mutIndBlock is => .mutIndBlock (is.map Inductive.to)

def Const.lvlsAndType : Const → Option (List Name × ExprCid)
  | .axiom           x
  | .theorem         x
  | .opaque          x
  | .quotient        x
  | .definition      x
  | .inductiveProj   x
  | .constructorProj x
  | .recursorProj    x
  | .definitionProj  x => some (x.lvls, x.type)
  | .mutDefBlock     _ => none
  | .mutIndBlock     _ => none

def Const.name : Const → Name
  | .axiom           x
  | .theorem         x
  | .opaque          x
  | .quotient        x
  | .definition      x
  | .inductiveProj   x
  | .constructorProj x
  | .recursorProj    x
  | .definitionProj  x => x.name
  | .mutDefBlock     x =>
    let defs : List (List Name) := x.map (fun ds => ds.map (·.name))
    s!"mutual definitions {defs}" -- TODO
  | .mutIndBlock     x =>
    let inds : List Name := x.map (·.name)
    s!"mutual inductives {inds}" -- TODO

def Const.ctorName : Const → String
  | .axiom           _ => "axiom"
  | .theorem         _ => "theorem"
  | .opaque          _ => "opaque"
  | .quotient        _ => "quotient"
  | .definition      _ => "definition"
  | .inductiveProj   _ => "inductiveProj"
  | .constructorProj _ => "constructorProj"
  | .recursorProj    _ => "recursorProj"
  | .definitionProj  _ => "definitionProj"
  | .mutDefBlock     _ => "mutDefBlock"
  | .mutIndBlock     _ => "mutIndBlock"

end Yatima
