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
  deriving Repr, Ord

structure Theorem (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  value : ExprCid k
  deriving Repr, Ord

structure Opaque (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  value : ExprCid k
  safe  : Boolₐ k
  deriving Repr, Ord

structure Quotient (k : Kind) where
  name : Nameₘ k
  lvls : NatₐListNameₘ k
  type : ExprCid k
  kind : Split QuotKind Unit k
  deriving Ord

structure Definition (k : Kind) where
  name   : Nameₘ k
  lvls   : NatₐListNameₘ k
  type   : ExprCid k
  value  : ExprCid k
  safety : Split DefinitionSafety Unit k
  deriving Inhabited, Ord

structure DefinitionProj (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  block : ConstCid k
  idx   : Nat
  deriving Repr, Ord

structure Constructor (k : Kind) where
  name   : Nameₘ k
  lvls   : NatₐListNameₘ k
  type   : ExprCid k
  idx    : Natₐ k
  params : Natₐ k
  fields : Natₐ k
  safe   : Boolₐ k
  deriving Repr, Ord

structure RecursorRule (k : Kind) where
  fields : Natₐ k
  rhs    : ExprCid k
  deriving Repr, Ord

-- For some reason, Lean cannot infer `Ord` when we use `Option`, so
-- we will will have to write our own `Ord` instance
instance [Ord α] : Ord (Option α) where
  compare a b :=
    let toList x := match x with
      | none => []
      | some x => [x]
    compare (toList a) (toList b)

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
  extInd   : Option (ConstCid k)
  deriving Repr, Ord

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
  deriving Inhabited, Ord

instance : Repr (Inductive k) where
  reprPrec a n := reprPrec a.name n

structure InductiveProj (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  block : ConstCid k
  idx   : Natₐ k
  deriving Repr, Ord

structure ConstructorProj (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  block : ConstCid k
  idx   : Natₐ k
  cidx  : Natₐ k
  deriving Repr, Ord

structure RecursorProj (k : Kind) where
  name  : Nameₘ k
  lvls  : NatₐListNameₘ k
  type  : ExprCid k
  block : ConstCid k
  idx   : Natₐ k
  ridx  : Natₐ k
  deriving Repr, Ord

instance : Repr (Quotient k) where
  reprPrec a n := reprPrec a.name n

/-- Parametric representation of constants for IPLD -/
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
  deriving Ord

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
  all    : List ConstIdx
  deriving BEq

structure Constructor where
  name   : Name
  lvls   : List Name
  type   : Expr
  idx    : Nat
  params : Nat
  fields : Nat
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
  struct  : Option ConstIdx
  deriving BEq

structure RecursorRule where
  fields : Nat
  rhs    : Expr
  deriving BEq

structure Recursor where
  name     : Name
  lvls     : List Name
  type     : Expr
  params   : Nat
  indices  : Nat
  motives  : Nat
  minors   : Nat
  rules    : List RecursorRule
  isK      : Bool
  ind      : ConstIdx
  internal : Bool
  -- we need to cache a list of the indexes of all of the recursors
  -- of this inductive in order to avoid infinite loops while typechecking
  all    : List ConstIdx
  deriving BEq

structure Quotient where
  name : Name
  lvls : List Name
  type : Expr
  kind : QuotKind
  deriving BEq

/-- Representation of constants for typechecking and transpilation -/
inductive Const
  | «axiom»     : Axiom → Const
  | «theorem»   : Theorem → Const
  | «inductive» : Inductive → Const
  | «opaque»    : Opaque → Const
  | definition  : Definition → Const
  | constructor : Constructor → Const
  | recursor    : Recursor → Const
  | quotient    : Quotient → Const
  deriving Inhabited, BEq

namespace Const

def name : Const → Name
  | .axiom       x
  | .theorem     x
  | .opaque      x
  | .inductive   x
  | .definition  x
  | .constructor x
  | .recursor x
  | .quotient    x => x.name

def type : Const → Expr
  | .axiom       x
  | .theorem     x
  | .inductive   x
  | .opaque      x
  | .definition  x
  | .constructor x
  | .recursor x
  | .quotient    x => x.type

def levels : Const → List Name
  | .axiom       x
  | .theorem     x
  | .inductive   x
  | .opaque      x
  | .definition  x
  | .constructor x
  | .recursor x
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

def Opaque.toIR (d : Opaque) (typeCid valueCid: IR.BothExprCid) : IR.Opaque k :=
  match k with
  | .anon => ⟨(), d.lvls.length, typeCid.anon, valueCid.anon, d.safe⟩
  | .meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta, ()⟩

def Quotient.toIR (d : Quotient) (typeCid : IR.BothExprCid) : IR.Quotient k :=
  match k with
  | .anon => ⟨(), d.lvls.length, typeCid.anon, d.kind⟩
  | .meta => ⟨d.name, d.lvls, typeCid.meta, ()⟩

def Axiom.toIR (d : Axiom) (typeCid : IR.BothExprCid) : IR.Axiom k :=
  match k with
  | .anon => ⟨(), d.lvls.length, typeCid.anon, d.safe⟩
  | .meta => ⟨d.name, d.lvls, typeCid.meta, ()⟩

def Theorem.toIR (d : Theorem) (typeCid valueCid : IR.BothExprCid) : IR.Theorem k :=
  match k with
  | .anon => ⟨(), d.lvls.length, typeCid.anon, valueCid.anon⟩
  | .meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta⟩

def Definition.toIR (d : Definition) (typeCid valueCid : IR.BothExprCid) : IR.Definition k :=
  match k with
  | .anon => ⟨(), d.lvls.length, typeCid.anon, valueCid.anon, d.safety⟩
  | .meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta, ()⟩

def Constructor.toIR (c : Constructor) (typeCid : IR.BothExprCid) : IR.Constructor k :=
  match k with
  | .anon => ⟨(), c.lvls.length, typeCid.anon, c.idx, c.params, c.fields, c.safe⟩
  | .meta => ⟨c.name, c.lvls, typeCid.meta, (), (), (), ()⟩

def RecursorRule.toIR (r : RecursorRule) (rhsCid : IR.BothExprCid) : IR.RecursorRule k :=
  match k with
  | .anon => ⟨r.fields, rhsCid.anon⟩
  | .meta => ⟨(), rhsCid.meta⟩

-- def ExtRecursor.toIR {k : IR.Kind} (r : ExtRecursor) (typeCid : IR.BothExprCid)
--     (rulesCids : List $ IR.RecursorRule k) : IR.Recursor .extr k :=
--   match k with
--   | .anon => ⟨(), r.lvls.length, typeCid.anon, r.params, r.indices, r.motives,
--     r.minors, rulesCids, r.k⟩
--   | .meta => ⟨r.name, r.lvls, typeCid.meta, (), (), (), (), rulesCids, ()⟩

-- def IntRecursor.toIR {k : IR.Kind} (r : IntRecursor) (typeCid : IR.BothExprCid) :
--     IR.Recursor .intr k :=
--   match k with
--   | .anon => ⟨(), r.lvls.length, typeCid.anon, r.params, r.indices, r.motives,
--     r.minors, (), r.k⟩
--   | .meta => ⟨r.name, r.lvls, typeCid.meta, (), (), (), (), (), ()⟩

def Inductive.toIR (i : Inductive) (idx : Nat)
    (typeCid : IR.BothExprCid) (blockCid : IR.BothConstCid) : IR.InductiveProj k :=
  match k with
  | .anon => ⟨(), i.lvls.length, typeCid.anon, blockCid.anon, idx⟩
  | .meta => ⟨i.name, i.lvls, typeCid.meta, blockCid.meta, ()⟩

end TC

end Yatima
