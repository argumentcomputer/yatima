import Ipld.DagCbor
import Yatima.Datatypes.Store

namespace Yatima

namespace Ipld

open IR

instance : Coe Nat Ipld where
  coe x := .bytes x.toByteArrayBE

instance : Coe Bool Ipld where
  coe x := .bool x

def partitionName (name : Name) : List (String ⊕ Nat) :=
  let rec aux (acc : List (String ⊕ Nat)) : Name → List (String ⊕ Nat)
    | .str name s => aux ((.inl s) :: acc) name
    | .num name n => aux ((.inr n) :: acc) name
    | .anonymous  => acc
  aux [] name

instance : Coe Name Ipld where
  coe x := .array $ (partitionName x).foldl (init := #[]) fun acc y =>
    match y with
    | .inl s => acc.push (.string s)
    | .inr n => acc.push (.bytes n.toByteArrayBE)

instance : Coe (UnivCid  k) Ipld where coe u := .link u.data
instance : Coe (ExprCid  k) Ipld where coe u := .link u.data
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

instance : Coe Literal Ipld where coe
  | .natVal n => n
  | .strVal s => .string s

instance : Coe DefinitionSafety Ipld where coe
  | .safe    => .number 0
  | .unsafe  => .number 1
  | .partial => .number 2

instance [Coe α Ipld] [Coe β Ipld] : Coe (Split α β k) Ipld where coe
  | .injₗ a => .array #[.number 0, a]
  | .injᵣ b => .array #[.number 1, b]

instance : Coe Unit Ipld where coe
  | .unit => .null

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

def univToIpld : Univ k → Ipld
  | .zero     => .array #[.number $ UNIV k, .number 0]
  | .succ p   => .array #[.number $ UNIV k, .number 1, p]
  | .max a b  => .array #[.number $ UNIV k, .number 2, a, b]
  | .imax a b => .array #[.number $ UNIV k, .number 3, a, b]
  | .var n    => .array #[.number $ UNIV k, .number 4, n]

def exprToIpld : Expr k → Ipld
  | .var n i ls   => .array #[.number $ EXPR k, .number 0, n, i, ls]
  | .sort u       => .array #[.number $ EXPR k, .number 1, u]
  | .const n c ls => .array #[.number $ EXPR k, .number 2, n, c, ls]
  | .app f a      => .array #[.number $ EXPR k, .number 3, f, a]
  | .lam n i d b  => .array #[.number $ EXPR k, .number 4, n, i, d, b]
  | .pi n i d b   => .array #[.number $ EXPR k, .number 5, n, i, d, b]
  | .letE n t v b => .array #[.number $ EXPR k, .number 6, n, t, v, b]
  | .lit l        => .array #[.number $ EXPR k, .number 7, l]
  | .proj n e     => .array #[.number $ EXPR k, .number 8, n, e]

def constToIpld : Const k → Ipld
  | .axiom ⟨n, l, t, s⟩                 => .array #[.number $ CONST k, .number 0, n, l, t, s]
  | .theorem ⟨n, l, t, v⟩               => .array #[.number $ CONST k, .number 1, n, l, t, v]
  | .opaque ⟨n, l, t, v, s⟩             => .array #[.number $ CONST k, .number 2, n, l, t, v, s]
  | .quotient ⟨n, l, t, K⟩              => .array #[.number $ CONST k, .number 3, n, l, t, K]
  | .inductiveProj ⟨n, l, t, b, i⟩      => .array #[.number $ CONST k, .number 5, n, l, t, b, i]
  | .constructorProj ⟨n, l, t, b, i, j⟩ => .array #[.number $ CONST k, .number 6, n, l, t, b, i, j]
  | .recursorProj ⟨n, l, t, b, i, j⟩    => .array #[.number $ CONST k, .number 7, n, l, t, b, i, j]
  | .definitionProj ⟨n, l, t, b, i⟩     => .array #[.number $ CONST k, .number 8, n, l, t, b, i]
  | .mutDefBlock b                      => .array #[.number $ CONST k, .number 9, b]
  | .mutIndBlock b                      => .array #[.number $ CONST k, .number 10, b]

def ipldToCid (codec: Nat) (ipld : Ipld): Cid :=
  let cbor := DagCbor.serialize ipld;
  let hash := Multihash.sha3_256 cbor;
  { version := 0x01, codec, hash }

def univToCid (univ : Univ k) : Ipld × UnivCid k :=
  let ipld := univToIpld univ
  (ipld, ⟨ipldToCid (UNIV k).toNat ipld⟩)

def exprToCid (expr : Expr k) : Ipld × ExprCid k :=
  let ipld := exprToIpld expr
  (ipld, ⟨ipldToCid (EXPR k).toNat ipld⟩)

def constToCid (const : Const k) : Ipld × ConstCid k :=
  let ipld := constToIpld const
  (ipld, ⟨ipldToCid (CONST k).toNat ipld⟩)

def storeToIpld (store : Store) : Ipld :=
  .array #[
    .number STORE,
    .array store.consts,
    .array store.univAnon,
    .array store.exprAnon,
    .array store.constAnon,
    .array store.univMeta,
    .array store.exprMeta,
    .array store.constMeta]

end Ipld

end Yatima
