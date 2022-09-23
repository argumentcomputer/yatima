import Ipld.Cid
import Ipld.Ipld
import Ipld.DagCbor
import Ipld.Multihash
import Yatima.Datatypes.Univ
import Yatima.Datatypes.Expr
import Yatima.Datatypes.Const
import Yatima.Datatypes.Store

namespace Yatima

def Opaque.toIpld {k : Ipld.Kind} (d : Opaque) (typeCid valueCid: ExprCid) : Ipld.Opaque k :=
match k with
  | .anon => ⟨(), d.lvls.length, typeCid.anon, valueCid.anon, d.safe⟩
  | .meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta, ()⟩

def Quotient.toIpld {k : Ipld.Kind} (d : Quotient) (typeCid : ExprCid) : Ipld.Quotient k :=
match k with
  | .anon => ⟨(), d.lvls.length, typeCid.anon, d.kind⟩
  | .meta => ⟨d.name, d.lvls, typeCid.meta, ()⟩

def Axiom.toIpld {k : Ipld.Kind} (d : Axiom) (typeCid : ExprCid) : Ipld.Axiom k :=
match k with
  | .anon => ⟨(), d.lvls.length, typeCid.anon, d.safe⟩
  | .meta => ⟨d.name, d.lvls, typeCid.meta, ()⟩

def Theorem.toIpld {k : Ipld.Kind} (d : Theorem) (typeCid valueCid : ExprCid) : Ipld.Theorem k :=
match k with
  | .anon => ⟨(), d.lvls.length, typeCid.anon, valueCid.anon⟩
  | .meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta⟩

def Definition.toIpld {k : Ipld.Kind} (d : Definition) (typeCid valueCid : ExprCid) : Ipld.Definition k :=
match k with
  | .anon => ⟨(), d.lvls.length, typeCid.anon, valueCid.anon, d.safety⟩
  | .meta => ⟨d.name, d.lvls, typeCid.meta, valueCid.meta, ()⟩

def Constructor.toIpld {k : Ipld.Kind} (c : Constructor) (typeCid rhsCid : ExprCid) : Ipld.Constructor k :=
match k with
  | .anon => ⟨(), c.lvls.length, typeCid.anon, c.idx, c.params, c.fields, rhsCid.anon, c.safe⟩
  | .meta => ⟨c.name, c.lvls, typeCid.meta, (), (), (), rhsCid.meta, ()⟩

def RecursorRule.toIpld {k : Ipld.Kind} (r : RecursorRule) (ctorCid : ConstCid) (rhsCid : ExprCid) : Ipld.RecursorRule k :=
match k with
  | .anon => ⟨ctorCid.anon, r.fields, rhsCid.anon⟩
  | .meta => ⟨ctorCid.meta, (), rhsCid.meta⟩

def ExtRecursor.toIpld {k : Ipld.Kind} (r : ExtRecursor) (typeCid : ExprCid) (rulesCids : List $ Ipld.RecursorRule k) : Ipld.Recursor .extr k :=
match k with 
  | .anon =>
    ⟨ ()
    , r.lvls.length
    , typeCid.anon
    , r.params
    , r.indices
    , r.motives
    , r.minors
    , rulesCids
    , r.k ⟩
  | .meta =>
    ⟨ r.name
    , r.lvls
    , typeCid.meta
    , (), (), (), ()
    , rulesCids
    , ()⟩

def IntRecursor.toIpld {k : Ipld.Kind} (r : IntRecursor) (typeCid : ExprCid) : Ipld.Recursor .intr k :=
match k with 
  | .anon =>
    ⟨ ()
    , r.lvls.length
    , typeCid.anon
    , r.params
    , r.indices
    , r.motives
    , r.minors
    , .injₗ ()
    , r.k ⟩
  | .meta =>
    ⟨ r.name
    , r.lvls
    , typeCid.meta
    , (), (), (), ()
    , .injₗ ()
    , ()⟩

def Inductive.toIpld {k : Ipld.Kind} (i : Inductive) (idx : Nat) (typeCid : ExprCid) (blockCid : ConstCid) : Ipld.InductiveProj k :=
match k with
  | .anon =>
    ⟨ ()
    , i.lvls.length
    , typeCid.anon
    , blockCid.anon
    , idx ⟩
  | .meta =>
    ⟨ i.name
    , i.lvls
    , typeCid.meta
    , blockCid.meta
    , () ⟩

namespace Ipld

instance : Coe Nat Ipld where
  coe x := .bytes x.toByteArrayBE

instance : Coe Bool Ipld where
  coe x := .bool x

instance : Coe Name Ipld where
  coe x := .string (Lean.Name.toString x)

instance : Coe (UnivCid k)  Ipld where coe u := .link u.data
instance : Coe (ExprCid k)  Ipld where coe u := .link u.data
instance : Coe (ConstCid k) Ipld where coe u := .link u.data

instance [Coe α Ipld] [Coe β Ipld] : Coe (α ⊕ β) Ipld where coe
  | .inl a => a
  | .inr b => b

instance [Coe α Ipld] : Coe (Option α) Ipld where coe
  | none   => .null
  | some a => a

instance [Coe α Ipld] : Coe (List α) Ipld where
  coe l := .array ⟨l.map fun (x : α) => x⟩

instance [Coe α Ipld] [Coe β Ipld] : Coe (α × β) Ipld where
  coe x := .array #[x.1, x.2]

instance : Coe BinderInfo Ipld where coe
  | .default        => .number 0
  | .implicit       => .number 1
  | .strictImplicit => .number 2
  | .instImplicit   => .number 3
  | .auxDecl        => .number 4

instance : Coe Literal Ipld where coe
  | .natVal n => n
  | .strVal s => .string s

instance : Coe DefinitionSafety Ipld where coe
  | .safe    => .number 0
  | .unsafe  => .number 1
  | .partial => .number 2

instance [Coe A Ipld] [Coe B Ipld] : Coe (Split A B k) Ipld where coe
  | .injₗ a => .array #[.number 0, a]
  | .injᵣ b => .array #[.number 1, b]

instance : Coe Unit Ipld where coe
  | .unit => .array #[]

instance : (k : Kind) → Coe (RecursorRule k) Ipld
  | .anon => { coe := fun | .mk c f r => .array #[c, f, r] }
  | .meta => { coe := fun | .mk c f r => .array #[c, f, r] }

instance : Coe (Recursor b k) Ipld where coe
  | .mk n l t p i m m' rs k => .array #[n, l, t, p, i, m, m', rs, k]

instance : Coe (Sigma (Recursor · k)) Ipld where coe
  | .mk b (.mk n l t p i m m' rs k) => .array #[(b : Bool), n, l, t, p, i, m, m', rs, k]

instance : Coe (Constructor k) Ipld where coe
  | .mk n t l i p f r s => .array #[n, t, l, i, p, f, r, s]

instance : Coe (Inductive k) Ipld where coe
  | .mk n l t p i cs rs r s r' => .array #[n, l, t, p, i, cs, rs, r, s, r']

instance : Coe QuotKind Ipld where coe
  | .type => .number 0
  | .ctor => .number 1
  | .lift => .number 3
  | .ind  => .number 4

instance : Coe (Definition k) Ipld where coe
  | .mk n l t v s => .array #[n, l, t, v, s]

--instance : Coe (Ipld.ConstCid) Ipld where coe
--  | _ => sorry
--
--instance [Coe α Ipld] : Coe (Array α) Ipld where coe
--  | _ => sorry
--
--instance : Coe (Ipld.Both Ipld.ConstCid) Ipld where coe
--  | _ => sorry

end Ipld

namespace ToIpld

def ipldToCid (codec: Nat) (ipld : Ipld): Cid :=
  let cbor := DagCbor.serialize ipld;
  let hash := Multihash.sha3_256 cbor;
  { version := 0x01, codec, hash }

def univToIpld : (Ipld.Univ k) → Ipld
  | .zero     => .array #[.number $ Ipld.UNIV k, .number 0]
  | .succ p   => .array #[.number $ Ipld.UNIV k, .number 1, p]
  | .max a b  => .array #[.number $ Ipld.UNIV k, .number 2, a, b]
  | .imax a b => .array #[.number $ Ipld.UNIV k, .number 3, a, b]
  | .var n    => .array #[.number $ Ipld.UNIV k, .number 4, n]

def exprToIpld : (Ipld.Expr k) → Ipld
  | .var n i ls   => .array #[.number $ Ipld.EXPR k, .number 0, n, i, ls]
  | .sort u       => .array #[.number $ Ipld.EXPR k, .number 1, u]
  | .const n c ls => .array #[.number $ Ipld.EXPR k, .number 2, n, c, ls]
  | .app f a      => .array #[.number $ Ipld.EXPR k, .number 3, f, a]
  | .lam n i d b  => .array #[.number $ Ipld.EXPR k, .number 4, n, i, d, b]
  | .pi n i d c   => .array #[.number $ Ipld.EXPR k, .number 5, n, i, d, c]
  | .letE n t v b => .array #[.number $ Ipld.EXPR k, .number 6, n, t, v, b]
  | .lit l        => .array #[.number $ Ipld.EXPR k, .number 7, l]
  | .proj n e     => .array #[.number $ Ipld.EXPR k, .number 8, n, e]

def constToIpld : (Ipld.Const k) → Ipld
  | .axiom ⟨n, l, t, s⟩                 => .array #[.number $ Ipld.CONST k, .number 0, n, l, t, s]
  | .theorem ⟨n, l, t, v⟩               => .array #[.number $ Ipld.CONST k, .number 1, n, l, t, v]
  | .opaque ⟨n, l, t, v, s⟩             => .array #[.number $ Ipld.CONST k, .number 2, n, l, t, v, s]
  | .quotient ⟨n, l, t, K⟩              => .array #[.number $ Ipld.CONST k, .number 3, n, l, t, K]
  | .inductiveProj ⟨n, l, t, b, i⟩      => .array #[.number $ Ipld.CONST k, .number 5, n, l, t, b, i]
  | .constructorProj ⟨n, l, t, b, i, j⟩ => .array #[.number $ Ipld.CONST k, .number 6, n, l, t, b, i, j]
  | .recursorProj ⟨n, l, t, b, i, j⟩    => .array #[.number $ Ipld.CONST k, .number 7, n, l, t, b, i, j]
  | .definitionProj ⟨n, l, t, b, i⟩     => .array #[.number $ Ipld.CONST k, .number 8, n, l, t, b, i]
  | .mutDefBlock b                      => .array #[.number $ Ipld.CONST k, .number 9, b]
  | .mutIndBlock b                      => .array #[.number $ Ipld.CONST k, .number 10, b]

def bothConstCidToIpld (b : Ipld.Both Ipld.ConstCid) : Ipld :=
  let anonCid := b.anon
  let metaCid := b.meta
  .array #[anonCid.data.toString, metaCid.data.toString]

def univAnonToIpld (univPair : Ipld.UnivCid .anon × Ipld.Univ .anon) : Ipld :=
  let (univCid, univ) := univPair
  .array #[Ipld.link univCid.data, univToIpld univ]

def exprAnonToIpld (exprPair : Ipld.ExprCid .anon × Ipld.Expr .anon) : Ipld :=
  let (exprCid, expr) := exprPair
  .array #[Ipld.link exprCid.data, exprToIpld expr]

def constAnonToIpld (constPair : Ipld.ConstCid .anon × Ipld.Const .anon) : Ipld :=
  let (constCid, const) := constPair
  .array #[Ipld.link constCid.data, constToIpld const]

def univMetaToIpld (univPair : Ipld.UnivCid .meta × Ipld.Univ .meta) : Ipld :=
  let (univCid, univ) := univPair
  .array #[Ipld.link univCid.data, univToIpld univ]

def exprMetaToIpld (exprPair : Ipld.ExprCid .meta × Ipld.Expr .meta) : Ipld :=
  let (exprCid, expr) := exprPair
  .array #[Ipld.link exprCid.data, exprToIpld expr]

def constMetaToIpld (constPair : Ipld.ConstCid .meta × Ipld.Const .meta) : Ipld :=
  let (constCid, const) := constPair
  .array #[Ipld.link constCid.data, constToIpld const]

def storeToIpld (store: Ipld.Store) : Ipld :=
  let constsIpld := Array.mk $ store.consts.toList.map bothConstCidToIpld
  let univAnonIpld := Array.mk $ store.univ_anon.toList.map univAnonToIpld
  let exprAnonIpld := Array.mk $ store.univ_anon.toList.map univAnonToIpld
  let constAnonIpld := Array.mk $ store.univ_anon.toList.map univAnonToIpld
  let univMetaIpld:= Array.mk $ store.univ_anon.toList.map univAnonToIpld
  let exprMetaIpld := Array.mk $ store.univ_anon.toList.map univAnonToIpld
  let constMetaIpld := Array.mk $ store.univ_anon.toList.map univAnonToIpld
  .array #[
    Ipld.number Ipld.STORE,
    .array constsIpld,
    .array univAnonIpld,
    .array exprAnonIpld,
    .array constAnonIpld,
    .array univMetaIpld,
    .array exprMetaIpld,
    .array constMetaIpld
  ]

def univToCid (univ : Ipld.Univ k) : Ipld.UnivCid k :=
  { data := ipldToCid (Ipld.UNIV k).toNat (univToIpld univ) }

def exprToCid (expr : Ipld.Expr k) : Ipld.ExprCid k :=
  { data := ipldToCid (Ipld.EXPR k).toNat (exprToIpld expr) }

def constToCid (const : Ipld.Const k) : Ipld.ConstCid k :=
  { data := ipldToCid (Ipld.CONST k).toNat (constToIpld const) }

-- toIpld Tests
open Std (RBMap RBTree)

def testExprAnon : Ipld.Expr .anon := Ipld.Expr.sort (univToCid Ipld.Univ.zero)
def testExprMeta : Ipld.Expr .meta := Ipld.Expr.sort (univToCid Ipld.Univ.zero)

def testSplit : (k : Bool) → Split Nat String k
  | true => .injₗ 0
  | false => .injᵣ "hi"

def testNameSplit : (k : Bool) → Split Unit Lean.Name k
  | true => .injₗ ()
  | false => .injᵣ "hi"

def testNatListNameSplit : (k : Bool) → Split Nat (List Lean.Name) k
  | true => .injₗ  0
  | false => .injᵣ ["hi"]

def testBoolSplit : (k : Bool) → Split Bool Unit k
  | true => .injₗ true
  | false => .injᵣ ()

def testConstAnon : Ipld.Const .anon :=
  let testAxiom : Ipld.Axiom .anon := {
    name := testNameSplit true,
    lvls := testNatListNameSplit true,
    type := exprToCid testExprAnon,
    safe := testBoolSplit true
  }
  Ipld.Const.axiom testAxiom

def testConstMeta : Ipld.Const .meta :=
  let testAxiom : Ipld.Axiom .meta := {
    name := testNameSplit false,
    lvls := testNatListNameSplit false,
    type := exprToCid testExprMeta,
    safe := testBoolSplit false
  }
  Ipld.Const.axiom testAxiom

def myConstCidAnon : Ipld.ConstCid .anon := constToCid testConstAnon
def myConstCidMeta : Ipld.ConstCid .meta := constToCid testConstMeta

def testConstBoth : Ipld.Both Ipld.ConstCid :=
  { anon:= myConstCidAnon, meta := myConstCidMeta }

def testConsts : RBTree (Ipld.Both Ipld.ConstCid) compare :=
  let const : Ipld.Both Ipld.ConstCid := testConstBoth
  .ofList [const]
def testUnivAnons : RBMap (Ipld.UnivCid .anon) (Ipld.Univ .anon) compare :=
  let univ : Ipld.Univ .anon := Ipld.Univ.zero
  .ofList [(univToCid univ, univ)]
def testExprAnons : RBMap (Ipld.ExprCid .anon) (Ipld.Expr .anon) compare :=
  let expr : Ipld.Expr .anon := testExprAnon
  .ofList [(exprToCid expr, expr)]
def testConstAnons : RBMap (Ipld.ConstCid .anon) (Ipld.Const .anon) compare :=
  let const : Ipld.Const .anon := testConstAnon
  .ofList [(constToCid const, const)]
def testUnivMetas : RBMap (Ipld.UnivCid .meta) (Ipld.Univ .meta) compare :=
  let univ : Ipld.Univ .meta := Ipld.Univ.zero
  .ofList [(univToCid univ, univ)]
def testExprMetas : RBMap (Ipld.ExprCid .meta) (Ipld.Expr .meta) compare :=
  let expr : Ipld.Expr .meta := testExprMeta
  .ofList [(exprToCid expr, expr)]
def testConstMetas : RBMap (Ipld.ConstCid .meta) (Ipld.Const .meta) compare :=
  let const : Ipld.Const .meta := testConstMeta
  .ofList [(constToCid const, const)]

def testStore : Ipld.Store :=
  {
    consts := testConsts,
    univ_anon := testUnivAnons,
    expr_anon := testExprAnons,
    const_anon := testConstAnons,
    univ_meta := testUnivMetas,
    expr_meta := testExprMetas,
    const_meta := testConstMetas
  }

#eval storeToIpld testStore

end ToIpld

end Yatima
