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
  | .Anon, d => ⟨.anon (), .anon d.lvls.length, d.type.anon, d.value.anon, .anon d.safety⟩
  | .Meta, d => ⟨.meta d.name, .meta d.lvls, d.type.meta, d.value.meta, .meta ()⟩

def Constructor.to : {k : Kind} → Constructor → Ipld.Constructor k
  | .Anon, x => ⟨.anon (), .anon x.lvls.length, x.type.anon, .anon x.params, .anon x.fields, x.rhs.anon⟩
  | .Meta, x => ⟨.meta x.name, .meta x.lvls, x.type.meta, .meta (), .meta (), x.rhs.meta⟩

def RecursorRule.to : {k : Kind} → RecursorRule → Ipld.RecursorRule k
  | .Anon, x => ⟨x.ctor.anon, .anon x.fields, x.rhs.anon⟩
  | .Meta, x => ⟨x.ctor.meta, .meta (), x.rhs.meta⟩

def Recursor.to : {k : Kind} → Recursor b → Ipld.Recursor k b
  | .Anon, x =>
    ⟨ .anon ()
    , .anon x.lvls.length
    , x.type.anon
    , .anon x.params
    , .anon x.indices
    , .anon x.motives
    , .anon x.minors
    , match b with
      | .Intr => .intr Unit.unit
      | .Extr => .extr $ x.rules.proj₂.map $ RecursorRule.to
    , .anon x.k ⟩
  | .Meta, x =>
    ⟨.meta x.name
    , .meta x.lvls
    , x.type.meta
    , .meta (), .meta (), .meta (), .meta ()
    , match b with
      | .Intr => .intr Unit.unit
      | .Extr => .extr $ x.rules.proj₂.map $ RecursorRule.to
    , .meta ()⟩

def Inductive.to : {k : Kind} → Inductive → Ipld.Inductive k
  | .Anon, x =>
    ⟨ .anon ()
    , .anon x.lvls.length
    , x.type.anon
    , .anon x.params
    , .anon x.indices
    , x.ctors.map (·.to)
    , x.recrs.map (fun p => .mk p.fst (Recursor.to p.snd))
    , .anon x.recr
    , .anon x.safe
    , .anon x.refl ⟩
  | .Meta, x =>
    ⟨ .meta x.name
    , .meta x.lvls
    , x.type.meta
    , .meta () , .meta ()
    , x.ctors.map (·.to)
    , x.recrs.map (fun p => .mk p.fst (Recursor.to p.snd))
    , .meta () , .meta () , .meta () ⟩

def Const.to : {k : Kind} → Const → Ipld.Const k
  | .Anon, .axiom a => .axiom ⟨.anon (), .anon a.lvls.length, a.type.anon, .anon a.safe⟩
  | .Meta, .axiom a => .axiom ⟨.meta a.name, .meta a.lvls, a.type.meta, .meta ()⟩
  | .Anon, .theorem t => .theorem ⟨.anon (), .anon t.lvls.length, t.type.anon, t.value.anon⟩
  | .Meta, .theorem t => .theorem ⟨.meta t.name, .meta t.lvls, t.type.meta, t.value.meta⟩
  | .Anon, .opaque o => .opaque ⟨.anon (), .anon o.lvls.length, o.type.anon, o.value.anon, .anon o.safe⟩
  | .Meta, .opaque o => .opaque ⟨.meta o.name, .meta o.lvls, o.type.meta, o.value.meta, .meta ()⟩
  | .Anon, .quotient q => .quotient ⟨.anon (), .anon q.lvls.length, q.type.anon, .anon q.kind⟩
  | .Meta, .quotient q => .quotient ⟨.meta q.name, .meta q.lvls, q.type.meta, .meta ()⟩
  | .Anon, .definition d => .definition d.to
  | .Meta, .definition d => .definition d.to
  | .Anon, .inductiveProj i => .inductiveProj
    ⟨ .anon () , .anon i.lvls.length , i.type.anon , i.block.anon , .anon i.idx ⟩
  | .Meta, .inductiveProj i => .inductiveProj
    ⟨ .meta i.name , .meta i.lvls , i.type.meta , i.block.meta , .meta () ⟩
  | .Anon, .constructorProj c => .constructorProj
    ⟨ .anon () , .anon c.lvls.length , c.type.anon , c.block.anon , .anon c.idx , .anon c.cidx ⟩
  | .Meta, .constructorProj c => .constructorProj
    ⟨ .meta c.name , .meta c.lvls , c.type.meta , c.block.meta , .meta () , .meta () ⟩
  | .Anon, .recursorProj r => .recursorProj
    ⟨ .anon () , .anon r.lvls.length , r.type.anon , r.block.anon , .anon r.idx , .anon r.ridx ⟩
  | .Meta, .recursorProj r => .recursorProj
    ⟨ .meta r.name , .meta r.lvls , r.type.meta , r.block.meta , .meta () , .meta () ⟩
  | .Anon, .definitionProj x => .definitionProj
    ⟨ .anon () , .anon x.lvls.length , x.type.anon , x.block.anon , .anon x.idx ⟩
  | .Meta, .definitionProj x => .definitionProj
    ⟨ .meta x.name , .meta x.lvls , x.type.meta , x.block.meta , .meta () ⟩
  | .Anon, .mutDefBlock ds => .mutDefBlock $
    (ds.map fun ds => match ds.head? with | some d => [d] | none => []).join.map (.anon ∘ Definition.to)
  | .Meta, .mutDefBlock ds => .mutDefBlock $ ds.map fun ds => .meta $ ds.map $ Definition.to
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
