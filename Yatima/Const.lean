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

structure DefinitionProj where
  name  : Name
  lvls  : List Name
  type  : ExprCid
  block : ConstCid
  idx   : Nat

structure DefinitionProjAnon where
  lvls  : Nat
  type  : ExprAnonCid
  block : ConstAnonCid
  idx   : Nat

structure DefinitionProjMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  block : ConstMetaCid

structure Constructor where
  name   : Name
  lvls   : List Name
  type   : ExprCid
  params : Nat
  fields : Nat
  rhs    : ExprCid

structure ConstructorAnon where
  lvls   : Nat
  type   : ExprAnonCid
  params : Nat
  fields : Nat
  rhs    : ExprAnonCid
  deriving Inhabited

structure ConstructorMeta where
  name   : Name
  lvls   : List Name
  type   : ExprMetaCid
  rhs    : ExprMetaCid
  deriving Inhabited

structure RecursorRule where
  ctor   : ConstCid
  fields : Nat
  rhs    : ExprCid

structure RecursorRuleAnon where
  ctor   : ConstAnonCid
  fields : Nat
  rhs    : ExprAnonCid

structure RecursorRuleMeta where
  ctor   : ConstMetaCid
  rhs    : ExprMetaCid

structure Recursor (b : Bool) where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : match b with | .true => Unit | .false => List RecursorRule
  k       : Bool

structure RecursorAnon (b : Bool) where
  lvls    : Nat
  type    : ExprAnonCid
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : match b with | .true => Unit | .false => List RecursorRuleAnon
  k       : Bool

structure RecursorMeta (b : Bool) where
  name    : Name
  lvls    : List Name
  type    : ExprMetaCid
  rules   : match b with | .true => Unit | .false => List RecursorRuleMeta

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

structure InductiveAnon where
  lvls     : Nat
  type     : ExprAnonCid
  params   : Nat
  indices  : Nat
  ctors    : List ConstructorAnon
  recrs    : List (Sigma RecursorAnon)
  recr     : Bool
  safe     : Bool
  refl     : Bool
  deriving Inhabited

structure InductiveMeta where
  name     : Name
  lvls     : List Name
  type     : ExprMetaCid
  ctors    : List ConstructorMeta
  recrs    : List (Sigma RecursorMeta)
  deriving Inhabited

structure InductiveProj where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  block   : ConstCid
  idx     : Nat

structure InductiveProjAnon where
  lvls    : Nat
  type    : ExprAnonCid
  block   : ConstAnonCid
  idx     : Nat

structure InductiveProjMeta where
  name    : Name
  lvls    : List Name
  type    : ExprMetaCid
  block   : ConstMetaCid

structure ConstructorProj where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  block   : ConstCid
  idx     : Nat
  cidx    : Nat

structure ConstructorProjAnon where
  lvls    : Nat
  type    : ExprAnonCid
  block   : ConstAnonCid
  idx     : Nat
  cidx    : Nat

structure ConstructorProjMeta where
  name    : Name
  lvls    : List Name
  type    : ExprMetaCid
  block   : ConstMetaCid

structure RecursorProj where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  block   : ConstCid
  idx     : Nat
  ridx    : Nat

structure RecursorProjAnon where
  lvls    : Nat
  type    : ExprAnonCid
  block   : ConstAnonCid
  idx     : Nat
  ridx    : Nat

structure RecursorProjMeta where
  name    : Name
  lvls    : List Name
  type    : ExprMetaCid
  block   : ConstMetaCid

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
  -- standalone constants
  | «axiom»     : Axiom → Const
  | «theorem»   : Theorem → Const
  | «opaque»      : Opaque → Const
  | quotient    : Quotient → Const
  | definition  : Definition → Const
  -- projections of mutual blocks
  | inductiveProj   : InductiveProj → Const
  | constructorProj : ConstructorProj → Const
  | recursorProj    : RecursorProj → Const
  | definitionProj  : DefinitionProj → Const
  -- constants to represent mutual blocks
  | mutDefBlock : List (List Definition) → Const
  | mutIndBlock : List Inductive → Const

inductive ConstAnon
  | «axiom»     : AxiomAnon → ConstAnon
  | «theorem»   : TheoremAnon → ConstAnon
  | «opaque»      : OpaqueAnon → ConstAnon
  | quotient    : QuotientAnon → ConstAnon
  | definition  : DefinitionAnon → ConstAnon
  | inductiveProj   : InductiveProjAnon → ConstAnon
  | constructorProj : ConstructorProjAnon → ConstAnon
  | recursorProj    : RecursorProjAnon → ConstAnon
  | definitionProj  : DefinitionProjAnon → ConstAnon
  | mutDefBlock : List DefinitionAnon → ConstAnon
  | mutIndBlock : List InductiveAnon → ConstAnon

inductive ConstMeta
  | «axiom»     : AxiomMeta → ConstMeta
  | «theorem»   : TheoremMeta → ConstMeta
  | «opaque»      : OpaqueMeta → ConstMeta
  | quotient    : QuotientMeta → ConstMeta
  | definition  : DefinitionMeta → ConstMeta
  | inductiveProj   : InductiveProjMeta → ConstMeta
  | constructorProj : ConstructorProjMeta → ConstMeta
  | recursorProj    : RecursorProjMeta → ConstMeta
  | definitionProj  : DefinitionProjMeta → ConstMeta
  | mutDefBlock : List (List DefinitionMeta) → ConstMeta
  | mutIndBlock : List InductiveMeta → ConstMeta

def Definition.toAnon (d : Definition) : DefinitionAnon :=
  ⟨d.lvls.length, d.type.anon, d.value.anon, d.safety⟩

def Constructor.toAnon (x : Constructor) : ConstructorAnon :=
  ⟨x.lvls.length, x.type.anon, x.params, x.fields, x.rhs.anon⟩

def RecursorRule.toAnon (x : RecursorRule) : RecursorRuleAnon :=
  ⟨x.ctor.anon, x.fields, x.rhs.anon⟩

def Recursor.toAnon (x: Recursor b) : RecursorAnon b :=
  ⟨ x.lvls.length
  , x.type.anon
  , x.params
  , x.indices
  , x.motives
  , x.minors
  , match b with
    | .true => Unit.unit
    | .false => x.rules.map RecursorRule.toAnon
  , x.k ⟩

def Inductive.toAnon (x: Inductive) : InductiveAnon :=
  ⟨ x.lvls.length
  , x.type.anon
  , x.params
  , x.indices
  , x.ctors.map (·.toAnon)
  , x.recrs.map (fun p => .mk p.fst (Recursor.toAnon p.snd))
  , x.recr
  , x.safe
  , x.refl ⟩

def Const.toAnon : Const → ConstAnon
  | .axiom a => .axiom ⟨a.lvls.length, a.type.anon, a.safe⟩
  | .theorem t => .theorem ⟨t.lvls.length, t.type.anon, t.value.anon⟩
  | .opaque o => .opaque ⟨o.lvls.length, o.type.anon, o.value.anon, o.safe⟩
  | .quotient q => .quotient ⟨q.lvls.length, q.type.anon, q.kind⟩
  | .definition d => .definition d.toAnon
  | .inductiveProj i => .inductiveProj
    ⟨ i.lvls.length
    , i.type.anon
    , i.block.anon
    , i.idx ⟩
  | .constructorProj c => .constructorProj 
    ⟨ c.lvls.length
    , c.type.anon
    , c.block.anon
    , c.idx
    , c.cidx ⟩
  | .recursorProj r => .recursorProj
    ⟨ r.lvls.length
    , r.type.anon
    , r.block.anon
    , r.idx
    , r.ridx ⟩
  | .definitionProj x => .definitionProj
    ⟨ x.lvls.length
    , x.type.anon
    , x.block.anon
    , x.idx ⟩
  | .mutDefBlock ds => .mutDefBlock $
    (ds.map fun ds => match ds.head? with | some d => [d] | none => []).join.map
      Definition.toAnon
  | .mutIndBlock is => .mutIndBlock (is.map Inductive.toAnon)

def Definition.toMeta (d: Definition) : DefinitionMeta :=
  ⟨d.name, d.lvls, d.type.meta, d.value.meta⟩

def Constructor.toMeta (x: Constructor) : ConstructorMeta :=
  ⟨x.name, x.lvls, x.type.meta, x.rhs.meta⟩

def RecursorRule.toMeta (x: RecursorRule) : RecursorRuleMeta :=
  ⟨x.ctor.meta, x.rhs.meta⟩

def Recursor.toMeta (x: Recursor b) : RecursorMeta b :=
  ⟨x.name, x.lvls, x.type.meta, match b with | .true => Unit.unit | .false => x.rules.map RecursorRule.toMeta⟩

def Inductive.toMeta (x: Inductive) : InductiveMeta :=
  ⟨ x.name
  , x.lvls
  , x.type.meta
  , x.ctors.map (·.toMeta)
  , x.recrs.map (fun p => .mk p.fst (Recursor.toMeta p.snd)) ⟩

def Const.toMeta : Const → ConstMeta
  | .axiom a => .axiom ⟨a.name, a.lvls, a.type.meta⟩
  | .theorem t => .theorem ⟨t.name, t.lvls, t.type.meta, t.value.meta⟩
  | .opaque o => .opaque ⟨o.name, o.lvls, o.type.meta, o.value.meta⟩
  | .quotient q => .quotient ⟨q.name, q.lvls, q.type.meta⟩
  | .definition d => .definition d.toMeta
  | .inductiveProj i => .inductiveProj
    ⟨ i.name
    , i.lvls
    , i.type.meta
    , i.block.meta ⟩
  | .constructorProj c => .constructorProj
    ⟨ c.name
    , c.lvls
    , c.type.meta
    , c.block.meta ⟩
  | .recursorProj r => .recursorProj ⟨r.name, r.lvls, r.type.meta, r.block.meta⟩
  | .definitionProj x => .definitionProj
    ⟨ x.name
    , x.lvls
    , x.type.meta
    , x.block.meta ⟩
  | .mutDefBlock ds => .mutDefBlock $ ds.map fun ds => ds.map Definition.toMeta
  | .mutIndBlock is => .mutIndBlock (is.map Inductive.toMeta)

def Const.lvlsAndType : Const → Option ((List Name) × ExprCid)
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
  | .mutDefBlock     x => s!"mutual definitions {x.map fun ds => ds.map (·.name)}" -- TODO
  | .mutIndBlock     x => s!"mutual inductives {x.map (·.name)}" -- TODO

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
