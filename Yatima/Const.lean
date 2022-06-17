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

structure MutualTheoremBlock where
  thms : List Theorem

structure MutualTheoremBlockAnon where
  thms : List TheoremAnon

structure MutualTheoremBlockMeta where
  thms : List TheoremMeta

structure MutualTheorem where
  block : ConstCid
  name  : Name
  idx   : Nat

structure MutualTheoremAnon where
  block : ConstAnonCid
  idx   : Nat

structure MutualTheoremMeta where
  block : ConstMetaCid
  name  : Name

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

structure MutualDefinitionBlock where
  defs : List Definition

structure MutualDefinitionBlockAnon where
  defs : List DefinitionAnon

structure MutualDefinitionBlockMeta where
  defs : List DefinitionMeta

structure MutualDefinition where
  block : ConstCid
  name  : Name
  idx   : Nat

structure MutualDefinitionAnon where
  block : ConstAnonCid
  idx   : Nat

structure MutualDefinitionMeta where
  block : ConstMetaCid
  name  : Name

structure Inductive where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  params  : Nat
  indices : Nat
  ctors   : List (Name × ExprCid)
  recr    : Bool
  safe    : Bool
  refl    : Bool
  nest    : Bool

structure InductiveAnon where
  lvls    : Nat
  type    : ExprAnonCid
  params  : Nat
  indices : Nat
  ctors   : List (Name × ExprAnonCid)
  recr    : Bool
  safe    : Bool
  refl    : Bool
  nest    : Bool

structure InductiveMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  ctors : List ExprMetaCid

structure Constructor where
  name   : Name
  lvls   : List Name
  type   : ExprCid
  ind    : ConstCid
  idx    : Nat
  params : Nat
  fields : Nat
  safe   : Bool

structure ConstructorAnon where
  lvls   : Nat
  type   : ExprAnonCid
  ind    : ConstAnonCid
  idx    : Nat
  params : Nat
  fields : Nat
  safe   : Bool

structure ConstructorMeta where
  name : Name
  lvls : List Name
  type : ExprMetaCid
  ind  : ConstMetaCid

structure RecursorRule where
  ctor   : ConstCid
  fields : Nat
  rhs    : ExprCid

structure RecursorRuleAnon where
  ctor   : ConstAnonCid
  fields : Nat
  rhs    : ExprAnonCid

structure RecursorRuleMeta where
  ctor : ConstMetaCid
  rhs  : ExprMetaCid

structure Recursor where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  ind     : ConstCid
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : List RecursorRule
  k       : Bool
  safe    : Bool

structure RecursorAnon where
  lvls    : Nat
  type    : ExprAnonCid
  ind     : ConstAnonCid
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : List RecursorRuleAnon
  k       : Bool
  safe    : Bool

structure RecursorMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  ind   : ConstMetaCid
  rules : List RecursorRuleMeta

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
  | «inductive» : Inductive → Const
  | opaque      : Opaque → Const
  | definition  : Definition → Const
  | constructor : Constructor → Const
  | recursor    : Recursor → Const
  | quotient    : Quotient → Const
  | mutDefBlock : MutualDefinitionBlock → Const
  | mutDef      : MutualDefinition → Const  
  | mutThmBlock : MutualTheoremBlock → Const
  | mutThm      : MutualTheorem → Const

inductive ConstAnon
  | «axiom»     : AxiomAnon → ConstAnon
  | «theorem»   : TheoremAnon → ConstAnon
  | «inductive» : InductiveAnon → ConstAnon
  | opaque      : OpaqueAnon → ConstAnon
  | definition  : DefinitionAnon → ConstAnon
  | constructor : ConstructorAnon → ConstAnon
  | recursor    : RecursorAnon → ConstAnon
  | quotient    : QuotientAnon → ConstAnon
  | mutDefBlock : MutualDefinitionBlockAnon → ConstAnon
  | mutDef      : MutualDefinitionAnon → ConstAnon  
  | mutThmBlock : MutualTheoremBlockAnon → ConstAnon
  | mutThm      : MutualTheoremAnon → ConstAnon

inductive ConstMeta
  | «axiom»     : AxiomMeta → ConstMeta
  | «theorem»   : TheoremMeta → ConstMeta
  | «inductive» : InductiveMeta → ConstMeta
  | opaque      : OpaqueMeta → ConstMeta
  | definition  : DefinitionMeta → ConstMeta
  | constructor : ConstructorMeta → ConstMeta
  | recursor    : RecursorMeta → ConstMeta
  | quotient    : QuotientMeta → ConstMeta
  | mutDefBlock : MutualDefinitionBlockMeta → ConstMeta
  | mutDef      : MutualDefinitionMeta → ConstMeta  
  | mutThmBlock : MutualTheoremBlockMeta → ConstMeta
  | mutThm      : MutualTheoremMeta → ConstMeta

def Definition.toAnon (d : Definition) : DefinitionAnon :=
  ⟨d.lvls.length, d.type.anon, d.value.anon, d.safety⟩

def Theorem.toAnon (t : Theorem) : TheoremAnon :=
  ⟨t.lvls.length, t.type.anon, t.value.anon⟩

def Const.toAnon : Const → ConstAnon
  | .axiom a => .axiom ⟨a.lvls.length, a.type.anon, a.safe⟩
  | .theorem t => .theorem t.toAnon
  | .inductive i => .inductive ⟨i.lvls.length, i.type.anon, i.params, i.indices,
    i.ctors.map fun (n, e) => (n, e.anon), i.recr, i.safe, i.refl, i.nest⟩
  | .opaque o => .opaque ⟨o.lvls.length, o.type.anon, o.value.anon, o.safe⟩
  | .definition d => .definition d.toAnon
  | .constructor c => .constructor ⟨c.lvls.length, c.type.anon, c.ind.anon,
    c.idx, c.params, c.fields, c.safe⟩
  | .recursor r => .recursor ⟨r.lvls.length, r.type.anon, r.ind.anon, r.params,
    r.indices, r.motives, r.minors,
    r.rules.map fun rl => ⟨rl.ctor.anon, rl.fields, rl.rhs.anon⟩, r.k, r.safe⟩
  | .quotient q => .quotient ⟨q.lvls.length, q.type.anon, q.kind⟩
  | .mutDefBlock x => .mutDefBlock ⟨List.map Definition.toAnon x.defs⟩
  | .mutDef x => .mutDef ⟨x.block.anon, x.idx⟩
  | .mutThmBlock x => .mutThmBlock ⟨List.map Theorem.toAnon x.thms⟩
  | .mutThm x => .mutThm ⟨x.block.anon, x.idx⟩

def Definition.toMeta (d : Definition) : DefinitionMeta :=
  ⟨d.name, d.lvls, d.type.meta, d.value.meta⟩

def Theorem.toMeta (t : Theorem) : TheoremMeta :=
  ⟨t.name, t.lvls, t.type.meta, t.value.meta⟩

def Const.toMeta : Const → ConstMeta
  | .axiom a => .axiom ⟨a.name, a.lvls, a.type.meta⟩
  | .theorem t => .theorem t.toMeta
  | .inductive i => .inductive ⟨i.name, i.lvls, i.type.meta, i.ctors.map (·.2.meta)⟩
  | .opaque o => .opaque ⟨o.name, o.lvls, o.type.meta, o.value.meta⟩
  | .definition d => .definition d.toMeta
  | .constructor c => .constructor ⟨c.name, c.lvls, c.type.meta, c.ind.meta⟩
  | .recursor r => .recursor ⟨r.name, r.lvls, r.type.meta, r.ind.meta,
    r.rules.map fun rl => ⟨rl.ctor.meta, rl.rhs.meta⟩⟩
  | .quotient q => .quotient ⟨q.name, q.lvls, q.type.meta⟩
  | .mutDefBlock x => .mutDefBlock ⟨List.map Definition.toMeta x.defs⟩
  | .mutDef x => .mutDef ⟨x.block.meta, x.name⟩
  | .mutThmBlock x => .mutThmBlock ⟨List.map Theorem.toMeta x.thms⟩
  | .mutThm x => .mutThm ⟨x.block.meta, x.name⟩

def Const.name : Const → Name
  | .axiom       a => a.name
  | .theorem     t => t.name
  | .inductive   i => i.name
  | .opaque      o => o.name
  | .definition  d => d.name
  | .constructor c => c.name
  | .recursor r => r.name
  | .quotient q => q.name
  | .mutDefBlock x => s!"mutual {x.defs.map (·.name)}" -- TODO
  | .mutDef x => x.name
  | .mutThmBlock x => s!"mutual {x.thms.map (·.name)}" -- TODO
  | .mutThm x => x.name

def Const.ctorName : Const → String
  | .axiom a => "axiom"
  | .theorem t => "theorem"
  | .inductive i => "inductive"
  | .opaque o => "opaque"
  | .definition d => "definition"
  | .constructor c => "constructor"
  | .recursor r => "recursor"
  | .quotient q => "quotient"
  | .mutDefBlock x => "mutDefBlock"
  | .mutDef x => "mutDef"
  | .mutThmBlock x => "mutThmBlock"
  | .mutThm x => "mutThm"

end Yatima
