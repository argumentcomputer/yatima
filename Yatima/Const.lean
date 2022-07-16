import Yatima.Kind
import Yatima.Name
import Yatima.Expr

namespace Yatima

def ListName? : Kind → Type
| .Anon => Nat
| _ => List Name

structure Axiom (k : Kind) where
  name : Name? k
  lvls : ListName? k
  type : ExprCid k
  safe : UnitIfMeta k Bool

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
  safe  : UnitIfMeta k Bool

inductive DefinitionSafety where
  | safe | «unsafe» | «partial»

structure Definition (k : Kind) where
  name   : Name? k
  lvls   : ListName? k
  type   : ExprCid k
  value  : ExprCid k
  safety : UnitIfMeta k DefinitionSafety

structure DefinitionProj (k : Kind) where
  name  : Name? k
  lvls  : ListName? k
  type  : ExprCid k
  block : ConstCid k
  idx   : UnitIfMeta k Nat

structure Constructor (k : Kind) where
  name   : Name? k
  lvls   : ListName? k
  type   : ExprCid k
  params : UnitIfMeta k Nat
  fields : UnitIfMeta k Nat
  rhs    : ExprCid k

structure RecursorRule (k : Kind) where
  ctor   : ConstCid k
  fields : UnitIfMeta k Nat
  rhs    : ExprCid k

structure Recursor (k : Kind) (b : Bool) where
  name    : Name? k
  lvls    : ListName? k
  type    : ExprCid k
  params  : UnitIfMeta k Nat
  indices : UnitIfMeta k Nat
  motives : UnitIfMeta k Nat
  minors  : UnitIfMeta k Nat
  rules   : match b with | .true => Unit | .false => List (RecursorRule k)
  k       : UnitIfMeta k Bool

structure Inductive (k : Kind) where
  name     : Name? k
  lvls     : ListName? k
  type     : ExprCid k
  params   : UnitIfMeta k Nat
  indices  : UnitIfMeta k Nat
  ctors    : List (Constructor k)
  recrs    : List (Sigma (Recursor k))
  recr     : UnitIfMeta k Bool
  safe     : UnitIfMeta k Bool
  refl     : UnitIfMeta k Bool

structure InductiveProj (k : Kind) where
  name    : Name? k
  lvls    : ListName? k
  type    : ExprCid k
  block   : ConstCid k
  idx     : UnitIfMeta k Nat

structure ConstructorProj (k : Kind) where
  name    : Name? k
  lvls    : ListName? k
  type    : ExprCid k
  block   : ConstCid k
  idx     : Nat
  cidx    : Nat

structure RecursorProj (k : Kind) where
  name    : Name? k
  lvls    : ListName? k
  type    : ExprCid k
  block   : ConstCid k
  idx     : UnitIfMeta k Nat
  ridx    : UnitIfMeta k Nat

inductive QuotKind where
  | type | ctor | lift | ind

structure Quotient (k : Kind) where
  name : Name? k
  lvls : ListName? k
  type : ExprCid k
  kind : UnitIfMeta k QuotKind

inductive Const (k : Kind)
  -- standalone constants
  | «axiom»     : Axiom k → Const k
  | «theorem»   : Theorem k → Const k
  | «opaque»      : Opaque k → Const k
  | quotient    : Quotient k → Const k
  | definition  : Definition k → Const k
  -- projections of mutual blocks
  | inductiveProj   : InductiveProj k → Const k
  | constructorProj : ConstructorProj k → Const k
  | recursorProj    : RecursorProj k → Const k
  | definitionProj  : DefinitionProj k → Const k
  -- constants to represent mutual blocks
  | mutDefBlock : List (substIfAnon k (Definition k) (List (Definition k))) → Const k
  | mutIndBlock : List (Inductive k) → Const k

def Definition.to : (k : Kind) → Definition .Pure → Definition k
  | .Pure, d => d
  | .Anon, d => ⟨(), d.lvls.length, d.type.anon, d.value.anon, d.safety⟩
  | .Meta, d => ⟨d.name, d.lvls, d.type.meta, d.value.meta, ()⟩

def Constructor.to : (k : Kind) → Constructor .Pure → Constructor k
  | .Pure, x => x
  | .Anon, x => ⟨(), x.lvls.length, x.type.anon, x.params, x.fields, x.rhs.anon⟩
  | .Meta, x => ⟨x.name, x.lvls, x.type.meta, (), (), x.rhs.meta⟩

def RecursorRule.to : (k : Kind) → RecursorRule .Pure → RecursorRule k
  | .Pure, x => x
  | .Anon, x => ⟨x.ctor.anon, x.fields, x.rhs.anon⟩
  | .Meta, x => ⟨x.ctor.meta, (), x.rhs.meta⟩

def Recursor.to : (k : Kind) → Recursor .Pure b → Recursor k b
  | .Pure, x => x
  | .Anon, x =>
    ⟨ ()
    , x.lvls.length
    , x.type.anon
    , x.params
    , x.indices
    , x.motives
    , x.minors
    , match b with
      | .true => Unit.unit
      | .false => x.rules.map $ RecursorRule.to .Anon
    , x.k ⟩
  | .Meta, x => ⟨x.name, x.lvls, x.type.meta, (), (), (), (), match b with | .true => Unit.unit | .false => x.rules.map $ RecursorRule.to .Meta, ()⟩

def Inductive.to : (k : Kind) → Inductive .Pure → Inductive k
  | .Pure, x => x
  | .Anon, x =>
    ⟨ ()
    , x.lvls.length
    , x.type.anon
    , x.params
    , x.indices
    , x.ctors.map (·.to .Anon)
    , x.recrs.map (fun p => .mk p.fst (Recursor.to .Anon p.snd))
    , x.recr
    , x.safe
    , x.refl ⟩
  | .Meta, x =>
    ⟨ x.name
    , x.lvls
    , x.type.meta
    , ()
    , ()
    , x.ctors.map (·.to .Meta)
    , x.recrs.map (fun p => .mk p.fst (Recursor.to .Meta p.snd))
    , ()
    , ()
    , () ⟩

def Const.to : (k : Kind) → Const .Pure → Const k
  | .Pure, c => c
  | .Anon, .axiom a => .axiom ⟨(), a.lvls.length, a.type.anon, a.safe⟩
  | .Meta, .axiom a => .axiom ⟨a.name, a.lvls, a.type.meta, ()⟩
  | .Anon, .theorem t => .theorem ⟨(), t.lvls.length, t.type.anon, t.value.anon⟩
  | .Meta, .theorem t => .theorem ⟨t.name, t.lvls, t.type.meta, t.value.meta⟩
  | .Anon, .opaque o => .opaque ⟨(), o.lvls.length, o.type.anon, o.value.anon, o.safe⟩
  | .Meta, .opaque o => .opaque ⟨o.name, o.lvls, o.type.meta, o.value.meta, ()⟩
  | .Anon, .quotient q => .quotient ⟨(), q.lvls.length, q.type.anon, q.kind⟩
  | .Meta, .quotient q => .quotient ⟨q.name, q.lvls, q.type.meta, ()⟩
  | .Anon, .definition d => .definition $ d.to .Anon
  | .Meta, .definition d => .definition $ d.to .Meta
  | .Anon, .inductiveProj i => .inductiveProj
    ⟨ ()
    , i.lvls.length
    , i.type.anon
    , i.block.anon
    , i.idx ⟩
  | .Meta, .inductiveProj i => .inductiveProj
    ⟨ i.name
    , i.lvls
    , i.type.meta
    , i.block.meta
    , () ⟩
  | .Anon, .constructorProj c => .constructorProj
    ⟨ ()
    , c.lvls.length
    , c.type.anon
    , c.block.anon
    , c.idx
    , c.cidx ⟩
  | .Meta, .constructorProj c => .constructorProj
    ⟨ c.name
    , c.lvls
    , c.type.meta
    , c.block.meta
    , c.idx
    , c.cidx ⟩
  | .Anon, .recursorProj r => .recursorProj
    ⟨ ()
    , r.lvls.length
    , r.type.anon
    , r.block.anon
    , r.idx
    , r.ridx ⟩
  | .Meta, .recursorProj r => .recursorProj
    ⟨ r.name
    , r.lvls
    , r.type.meta
    , r.block.meta
    , ()
    , () ⟩
  | .Anon, .definitionProj x => .definitionProj
    ⟨ ()
    , x.lvls.length
    , x.type.anon
    , x.block.anon
    , x.idx ⟩
  | .Meta, .definitionProj x => .definitionProj
    ⟨ x.name
    , x.lvls
    , x.type.meta
    , x.block.meta
    , () ⟩
  | .Anon, .mutDefBlock ds => .mutDefBlock $
    (ds.map fun ds => match ds.head? with | some d => [d] | none => []).join.map (Definition.to .Anon)
  | .Meta, .mutDefBlock ds => .mutDefBlock $ ds.map fun ds => ds.map $ Definition.to .Meta
  | .Anon, .mutIndBlock is => .mutIndBlock (is.map $ Inductive.to .Anon)
  | .Meta, .mutIndBlock is => .mutIndBlock (is.map $ Inductive.to .Meta)

def Const.lvlsAndType : Const .Pure → Option (List Name × ExprCid .Pure)
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

def Const.name : Const .Pure → Name
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

def Const.ctorName : Const .Pure → String
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
