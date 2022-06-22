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

structure MutualDefinition where
  name  : Name
  lvls  : List Name
  type  : ExprCid
  block : ConstCid
  idx   : Nat

structure MutualDefinitionAnon where
  lvls  : Nat
  type  : ExprAnonCid
  block : ConstAnonCid
  idx   : Nat

structure MutualDefinitionMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  block : ConstMetaCid

structure ConstructorInfo where
  name   : Name
  type   : ExprCid
  params : Nat
  fields : Nat

structure ConstructorInfoAnon where
  type   : ExprAnonCid
  params : Nat
  fields : Nat

structure ConstructorInfoMeta where
  name   : Name
  type   : ExprMetaCid

structure RecursorInfo where
  name    : Name
  type    : ExprCid
  motives : Nat
  minors  : Nat
  rules   : List ExprCid
  k       : Bool

structure RecursorInfoAnon where
  type    : ExprAnonCid
  motives : Nat
  minors  : Nat
  rules   : List ExprAnonCid
  k       : Bool

structure RecursorInfoMeta where
  name    : Name
  type    : ExprMetaCid
  rules   : List ExprMetaCid

structure InductiveInfo where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  params  : Nat
  indices : Nat
  ctors   : List ConstructorInfo
  recrs   : List RecursorInfo
  recr    : Bool
  safe    : Bool
  refl    : Bool
  nest    : Bool

structure InductiveInfoAnon where
  lvls    : Nat
  type    : ExprAnonCid
  params  : Nat
  indices : Nat
  ctors   : List ConstructorInfoAnon
  recrs   : List RecursorInfoAnon
  recr    : Bool
  safe    : Bool
  refl    : Bool
  nest    : Bool

structure InductiveInfoMeta where
  name    : Name
  lvls    : List Name
  type    : ExprMetaCid
  ctors   : List ConstructorInfoMeta
  recrs   : List RecursorInfoMeta

structure Inductive where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  block   : ConstCid
  ind     : Nat

structure InductiveAnon where
  lvls    : Nat
  type    : ExprAnonCid
  block   : ConstAnonCid
  ind     : Nat

structure InductiveMeta where
  name    : Name
  lvls    : List Name
  type    : ExprMetaCid
  block   : ConstMetaCid

structure Constructor where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  block   : ConstCid
  ind     : Nat
  idx     : Nat

structure ConstructorAnon where
  lvls    : Nat
  type    : ExprAnonCid
  block   : ConstAnonCid
  ind     : Nat
  idx     : Nat

structure ConstructorMeta where
  name    : Name
  lvls    : List Name
  type    : ExprMetaCid
  block   : ConstMetaCid

structure Recursor where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  block   : ConstCid
  ind     : Nat
  idx     : Nat

structure RecursorAnon where
  lvls    : Nat
  type    : ExprAnonCid
  block   : ConstAnonCid
  ind     : Nat
  idx     : Nat

structure RecursorMeta where
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
  | «axiom»     : Axiom → Const
  | «theorem»   : Theorem → Const
  | opaque      : Opaque → Const
  | definition  : Definition → Const
  | indBlock    : List InductiveInfo → Const
  | «inductive» : Inductive → Const
  | constructor : Constructor → Const
  | recursor    : Recursor → Const
  | quotient    : Quotient → Const
  | mutDefBlock : List Definition → Const
  | mutDef      : MutualDefinition → Const

inductive ConstAnon
  | «axiom»     : AxiomAnon → ConstAnon
  | «theorem»   : TheoremAnon → ConstAnon
  | opaque      : OpaqueAnon → ConstAnon
  | definition  : DefinitionAnon → ConstAnon
  | indBlock    : List InductiveInfoAnon → ConstAnon
  | «inductive» : InductiveAnon → ConstAnon
  | constructor : ConstructorAnon → ConstAnon
  | recursor    : RecursorAnon → ConstAnon
  | quotient    : QuotientAnon → ConstAnon
  | mutDefBlock : List DefinitionAnon → ConstAnon
  | mutDef      : MutualDefinitionAnon → ConstAnon

inductive ConstMeta
  | «axiom»     : AxiomMeta → ConstMeta
  | «theorem»   : TheoremMeta → ConstMeta
  | opaque      : OpaqueMeta → ConstMeta
  | definition  : DefinitionMeta → ConstMeta
  | indBlock    : List InductiveInfoMeta → ConstMeta
  | «inductive» : InductiveMeta → ConstMeta
  | constructor : ConstructorMeta → ConstMeta
  | recursor    : RecursorMeta → ConstMeta
  | quotient    : QuotientMeta → ConstMeta
  | mutDefBlock : List DefinitionMeta → ConstMeta
  | mutDef      : MutualDefinitionMeta → ConstMeta

def Definition.toAnon (d: Definition) : DefinitionAnon :=
  ⟨d.lvls.length, d.type.anon, d.value.anon, d.safety⟩

def ConstructorInfo.toAnon (x: ConstructorInfo) : ConstructorInfoAnon :=
  ⟨x.type.anon, x.params, x.fields⟩

def RecursorInfo.toAnon (x: RecursorInfo) : RecursorInfoAnon :=
  ⟨x.type.anon, x.motives, x.minors, x.rules.map (·.anon), x.k⟩

def InductiveInfo.toAnon (x: InductiveInfo) : InductiveInfoAnon :=
  ⟨x.lvls.length, x.type.anon, x.params, x.indices, x.ctors.map (·.toAnon), x.recrs.map (·.toAnon), x.recr, x.safe, x.refl, x.nest⟩

def Const.toAnon : Const → ConstAnon
  | .axiom a => .axiom ⟨a.lvls.length, a.type.anon, a.safe⟩
  | .theorem t => .theorem ⟨t.lvls.length, t.type.anon, t.value.anon⟩
  | .opaque o => .opaque ⟨o.lvls.length, o.type.anon, o.value.anon, o.safe⟩
  | .definition d => .definition d.toAnon
  | .indBlock is => .indBlock (is.map InductiveInfo.toAnon)
  | .inductive i => .inductive ⟨i.lvls.length, i.type.anon, i.block.anon, i.ind⟩
  | .constructor c => .constructor ⟨c.lvls.length, c.type.anon, c.block.anon, c.ind, c.idx⟩ 
  | .recursor r => .recursor ⟨r.lvls.length, r.type.anon, r.block.anon, r.ind, r.idx⟩
  | .quotient q => .quotient ⟨q.lvls.length, q.type.anon, q.kind⟩
  | .mutDefBlock ds => .mutDefBlock (ds.map Definition.toAnon)
  | .mutDef x => .mutDef ⟨x.lvls.length, x.type.anon, x.block.anon, x.idx⟩

def Definition.toMeta (d: Definition) : DefinitionMeta :=
  ⟨d.name, d.lvls, d.type.meta, d.value.meta⟩

def ConstructorInfo.toMeta (x: ConstructorInfo) : ConstructorInfoMeta :=
  ⟨x.name, x.type.meta⟩

def RecursorInfo.toMeta (x: RecursorInfo) : RecursorInfoMeta :=
  ⟨x.name, x.type.meta, x.rules.map (·.meta)⟩

def InductiveInfo.toMeta (x: InductiveInfo) : InductiveInfoMeta :=
  ⟨x.name, x.lvls, x.type.meta, x.ctors.map (·.toMeta), x.recrs.map (·.toMeta)⟩

def Const.toMeta : Const → ConstMeta
  | .axiom a => .axiom ⟨a.name, a.lvls, a.type.meta⟩
  | .theorem t => .theorem ⟨t.name, t.lvls, t.type.meta, t.value.meta⟩
  | .opaque o => .opaque ⟨o.name, o.lvls, o.type.meta, o.value.meta⟩
  | .definition d => .definition d.toMeta
  | .indBlock is => .indBlock (is.map InductiveInfo.toMeta)
  | .inductive i => .inductive ⟨i.name, i.lvls, i.type.meta, i.block.meta⟩
  | .constructor c => .constructor ⟨c.name, c.lvls, c.type.meta, c.block.meta⟩
  | .recursor r => .recursor ⟨r.name, r.lvls, r.type.meta, r.block.meta⟩
  | .quotient q => .quotient ⟨q.name, q.lvls, q.type.meta⟩
  | .mutDefBlock ds => .mutDefBlock (ds.map Definition.toMeta)
  | .mutDef x => .mutDef ⟨x.name, x.lvls, x.type.meta, x.block.meta⟩

def Const.name : Const → Name
  | .axiom       a => a.name
  | .theorem     t => t.name
  | .opaque      o => o.name
  | .definition  d => d.name
  | .indBlock   i =>  s!"mutual inductives {i.map (·.name)}" -- TODO
  | .inductive   i => i.name
  | .constructor c => c.name
  | .recursor r => r.name
  | .quotient q => q.name
  | .mutDefBlock x => s!"mutual definitions {x.map (·.name)}" -- TODO
  | .mutDef x => x.name

def Const.ctorName : Const → String
  | .axiom a => "axiom"
  | .theorem t => "theorem"
  | .opaque o => "opaque"
  | .definition d => "definition"
  | .inductive i => "inductive"
  | .indBlock i => "indBlock"
  | .constructor c => "constructor"
  | .recursor r => "recursor"
  | .quotient q => "quotient"
  | .mutDefBlock x => "mutDefBlock"
  | .mutDef x => "mutDef"

end Yatima
