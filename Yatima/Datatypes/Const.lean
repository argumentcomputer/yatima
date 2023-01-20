import Yatima.Datatypes.Expr

namespace Yatima

namespace IR

-- The number of universes for anon or their names for meta
scoped notation "NatₐListNameₘ" => Split Nat (List Name)

-- Boolean flags for anon
scoped notation "Boolₐ" => Split Bool Unit

structure Axiom (k : Kind) where
  name : Nameₘ k
  lvls : NatₐListNameₘ k
  type : ExprCid k
  safe : Boolₐ k
  deriving Repr, Ord, BEq

structure Theorem (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  value : ExprCid k
  deriving Repr, Ord, BEq

structure Opaque (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  value : ExprCid k
  safe  : Boolₐ k
  deriving Repr, Ord, BEq

structure Quotient (k : Kind) where
  name : Nameₘ k
  lvls : NatₐListNameₘ k
  type : ExprCid k
  kind : Split QuotKind Unit k
  deriving Ord, BEq

structure Definition (k : Kind) where
  name   : Nameₘ k
  lvls   : NatₐListNameₘ k
  type   : ExprCid k
  value  : ExprCid k
  safety : Split DefinitionSafety Unit k
  deriving Inhabited, Ord, BEq

structure DefinitionProj (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  block : ConstCid k
  idx   : Nat
  deriving Repr, Ord, BEq

structure Constructor (k : Kind) where
  name   : Nameₘ k
  lvls   : NatₐListNameₘ k
  type   : ExprCid k
  idx    : Natₐ k
  params : Natₐ k
  fields : Natₐ k
  safe   : Boolₐ k
  deriving Repr, Ord, BEq

structure RecursorRule (k : Kind) where
  fields : Natₐ k
  rhs    : ExprCid k
  deriving Repr, Ord, BEq

structure Recursor (k : Kind) where
  name     : Nameₘ k
  lvls     : NatₐListNameₘ k
  type     : ExprCid k
  params   : Natₐ k
  indices  : Natₐ k
  motives  : Natₐ k
  minors   : Natₐ k
  rules    : List (RecursorRule k)
  isK      : Boolₐ k
  internal : Boolₐ k
  deriving Repr, Ord, BEq

structure Inductive (k : Kind) where
  name    : Nameₘ k
  lvls    : NatₐListNameₘ k
  type    : ExprCid k
  params  : Natₐ k
  indices : Natₐ k
  ctors   : List (Constructor k)
  recrs   : List (Recursor k)
  recr    : Boolₐ k
  safe    : Boolₐ k
  refl    : Boolₐ k
  deriving Inhabited, Ord, BEq

instance : Repr (Inductive k) where
  reprPrec a n := reprPrec a.name n

structure InductiveProj (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  block : ConstCid k
  idx   : Natₐ k
  deriving Repr, Ord, BEq

structure ConstructorProj (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  block : ConstCid k
  idx   : Natₐ k
  cidx  : Natₐ k
  deriving Repr, Ord, BEq

structure RecursorProj (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  block : ConstCid k
  idx   : Natₐ k
  ridx  : Natₐ k
  deriving Repr, Ord, BEq

instance : Repr (Quotient k) where
  reprPrec a n := reprPrec a.name n

/-- Parametric representation of constants for IPLD -/
inductive Const (k : Kind) where
  -- standalone constants
  | «axiom»     : Axiom    k → Const k
  | «theorem»   : Theorem  k → Const k
  | «opaque»    : Opaque   k → Const k
  | quotient    : Quotient k → Const k
  -- projections of mutual blocks
  | inductiveProj   : InductiveProj   k → Const k
  | constructorProj : ConstructorProj k → Const k
  | recursorProj    : RecursorProj    k → Const k
  | definitionProj  : DefinitionProj  k → Const k
  -- constants to represent mutual blocks
  | mutDefBlock : List (Split (Definition k) (List (Definition k)) k) → Const k
  | mutIndBlock : List (Inductive k) → Const k
  deriving Ord, BEq

namespace Const

def isNotMutBlock : Const k → Bool
  | .mutDefBlock _
  | .mutIndBlock _ => false
  | _ => true

def ctorName : Const k → String
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

def name : Const .meta → Name
  | .axiom           x
  | .theorem         x
  | .opaque          x
  | .quotient        x
  | .definitionProj  x
  | .inductiveProj   x
  | .constructorProj x
  | .recursorProj    x => x.name.projᵣ
  | .mutDefBlock     _
  | .mutIndBlock     _ => .anonymous

end Const

end IR

namespace TC

open Lurk (F)

structure Axiom where
  lvls : Nat
  type : Expr
  safe : Bool
  deriving BEq, Repr

structure Theorem where
  lvls  : Nat
  type  : Expr
  value : Expr
  deriving BEq, Repr

structure Opaque where
  lvls  : Nat
  type  : Expr
  value : Expr
  safe  : Bool
  deriving BEq, Repr

deriving instance Repr for Lean.QuotKind

structure Quotient where
  lvls : Nat
  type : Expr
  kind : QuotKind
  deriving BEq, Repr

structure Definition where
  lvls   : Nat
  type   : Expr
  value  : Expr
  safety : DefinitionSafety
  deriving BEq, Repr

structure Constructor where
  lvls   : Nat
  type   : Expr
  idx    : Nat
  params : Nat
  fields : Nat
  safe   : Bool
  deriving BEq, Repr

structure RecursorRule where
  fields : Nat
  rhs    : Expr
  deriving BEq, Repr

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
  deriving BEq, Repr

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
  struct  : Option F
  deriving BEq, Repr

/-- Representation of constants for typechecking -/
inductive Const
  | «axiom»     : Axiom → Const
  | «theorem»   : Theorem → Const
  | «inductive» : Inductive → Const
  | «opaque»    : Opaque → Const
  | definition  : Definition → Const
  | constructor : Constructor → Const
  | recursor    : Recursor → Const
  | quotient    : Quotient → Const
  deriving BEq, Repr


namespace Const

--def name : Const → Name
--  | .axiom       x
--  | .theorem     x
--  | .opaque      x
--  | .inductive   x
--  | .definition  x
--  | .constructor x
--  | .recursor x
--  | .quotient    x => x.name

def type : Const → Expr
  | .axiom       x
  | .theorem     x
  | .inductive   x
  | .opaque      x
  | .definition  x
  | .constructor x
  | .recursor    x
  | .quotient    x => x.type

def levels : Const → Nat
  | .axiom       x
  | .theorem     x
  | .inductive   x
  | .opaque      x
  | .definition  x
  | .constructor x
  | .recursor    x
  | .quotient    x => x.lvls

def ctorName : Const → String
  | .axiom       _ => "axiom"
  | .theorem     _ => "theorem"
  | .opaque      _ => "opaque"
  | .definition  _ => "definition"
  | .inductive   _ => "inductive"
  | .constructor _ => "constructor"
  | .recursor    d => if d.internal then "internal recursor" else "external recursor"
  | .quotient    _ => "quotient"

end Const

--def Opaque.toIR (d : Opaque) (typeCid valueCid: IR.BothExprCid) : IR.Opaque k :=
--  match k with
--  | .anon => ⟨(), d.lvls, typeCid.anon, valueCid.anon, d.safe⟩
--  | .meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta, ()⟩
--
--def Quotient.toIR (d : Quotient) (typeCid : IR.BothExprCid) : IR.Quotient k :=
--  match k with
--  | .anon => ⟨(), d.lvls, typeCid.anon, d.kind⟩
--  | .meta => ⟨d.name, d.lvls, typeCid.meta, ()⟩
--
--def Axiom.toIR (d : Axiom) (typeCid : IR.BothExprCid) : IR.Axiom k :=
--  match k with
--  | .anon => ⟨(), d.lvls, typeCid.anon, d.safe⟩
--  | .meta => ⟨d.name, d.lvls, typeCid.meta, ()⟩
--
--def Theorem.toIR (d : Theorem) (typeCid valueCid : IR.BothExprCid) : IR.Theorem k :=
--  match k with
--  | .anon => ⟨(), d.lvls, typeCid.anon, valueCid.anon⟩
--  | .meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta⟩
--
--def Definition.toIR (d : Definition) (typeCid valueCid : IR.BothExprCid) : IR.Definition k :=
--  match k with
--  | .anon => ⟨(), d.lvls, typeCid.anon, valueCid.anon, d.safety⟩
--  | .meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta, ()⟩
--
--def Constructor.toIR (c : Constructor) (typeCid : IR.BothExprCid) : IR.Constructor k :=
--  match k with
--  | .anon => ⟨(), c.lvls, typeCid.anon, c.idx, c.params, c.fields, c.safe⟩
--  | .meta => ⟨c.name, c.lvls, typeCid.meta, (), (), (), ()⟩
--
--def RecursorRule.toIR (r : RecursorRule) (rhsCid : IR.BothExprCid) : IR.RecursorRule k :=
--  match k with
--  | .anon => ⟨r.fields, rhsCid.anon⟩
--  | .meta => ⟨(), rhsCid.meta⟩
--
--def Inductive.toIR (i : Inductive) (idx : Nat)
--    (typeCid : IR.BothExprCid) (blockCid : IR.BothConstCid) : IR.InductiveProj k :=
--  match k with
--  | .anon => ⟨(), i.lvls, typeCid.anon, blockCid.anon, idx⟩
--  | .meta => ⟨i.name, i.lvls, typeCid.meta, blockCid.meta, ()⟩

end TC

end Yatima
