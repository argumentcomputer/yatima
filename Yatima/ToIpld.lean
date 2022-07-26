import Ipld.Cid
import Ipld.Ipld
import Ipld.DagCbor
import Ipld.Multihash
import Yatima.Univ
import Yatima.Expr
import Yatima.Const

namespace Yatima

namespace Ipld
instance : Coe Nat Ipld where
  coe x := .bytes x.toByteArrayBE

instance : Coe Bool Ipld where
  coe x := .bool x

instance : Coe Name Ipld where
  coe x := .string x


instance : Coe (UnivCid k)  Ipld where coe u := .link u.data
instance : Coe (ExprCid k)  Ipld where coe u := .link u.data
instance : Coe (ConstCid k) Ipld where coe u := .link u.data

instance [Coe α Ipld] [Coe β Ipld] : Coe (α ⊕ β) Ipld where coe
  | .inl i => i
  | .inr c => c

instance [Coe α Ipld] : Coe (Option α) Ipld where coe
  | none   => .null
  | some a => a

instance [Coe α Ipld] : Coe (List α) Ipld where
  coe l := .array ⟨List.map (fun (x : α) => x) l⟩

instance [Coe α Ipld] [Coe β Ipld] : Coe (α × β) Ipld where
  coe x := .array #[x.1, x.2]

instance : Coe BinderInfo Ipld where coe
  | .default        => .number 0
  | .implicit       => .number 1
  | .strictImplicit => .number 2
  | .instImplicit   => .number 3
  | .auxDecl        => .number 4

instance : Coe LitType Ipld where coe
  | .nat => .number 0
  | .str => .number 1

instance : Coe Literal Ipld where coe
  | .nat n => n
  | .str s => s

instance : Coe DefinitionSafety Ipld where coe
  | .safe    => .number 0
  | .unsafe  => .number 1
  | .partial => .number 2

instance [Coe A Ipld] [Coe B Ipld] : Coe (Split A B k) Ipld where coe
  | .inj₁ a => .array #[.number 0, a]
  | .inj₂ b => .array #[.number 1, b]

instance : Coe Unit Ipld where coe
  | .unit => .array #[]

instance : (k : Kind) → Coe (RecursorRule k) Ipld
  | .Anon => { coe := fun | .mk c f r => .array #[c, f, r] }
  | .Meta => { coe := fun | .mk c f r => .array #[c, f, r] }

instance : Coe (Recursor k b) Ipld where coe
  | .mk n l t p i m m' rs k => .array #[n, l, t, p, i, m, m', rs, k]

instance : Coe (Sigma (Recursor k)) Ipld where coe
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

end Ipld
namespace ToIpld

def ipldToCid (codec: Nat) (ipld : Ipld): Cid :=
  let cbor := DagCbor.serialize ipld;
  let hash := Multihash.sha3_256 cbor;
  { version := 0x01, codec, hash }

def univToIpld : (Ipld.Univ k) → Ipld
  | .zero      => .array #[.number $ Ipld.UNIV k, .number 0]
  | .succ p    => .array #[.number $ Ipld.UNIV k, .number 1, p]
  | .max a b   => .array #[.number $ Ipld.UNIV k, .number 2, a, b]
  | .imax a b  => .array #[.number $ Ipld.UNIV k, .number 3, a, b]
  | .var n i   => .array #[.number $ Ipld.UNIV k, .number 4, n, i]

def exprToIpld : (Ipld.Expr k) → Ipld
  | .var _ i      => .array #[.number $ Ipld.EXPR k, .number 0, i]
  | .sort u       => .array #[.number $ Ipld.EXPR k, .number 1, u]
  | .const n c ls => .array #[.number $ Ipld.EXPR k, .number 2, n, c, ls]
  | .app f a      => .array #[.number $ Ipld.EXPR k, .number 3, f, a]
  | .lam n i d b  => .array #[.number $ Ipld.EXPR k, .number 4, n, i, d, b]
  | .pi n i d c   => .array #[.number $ Ipld.EXPR k, .number 5, n, i, d, c]
  | .letE n t v b => .array #[.number $ Ipld.EXPR k, .number 6, n, t, v, b]
  | .lit l        => .array #[.number $ Ipld.EXPR k, .number 7, l]
  | .lty l        => .array #[.number $ Ipld.EXPR k, .number 8, l]
  | .fix n b      => .array #[.number $ Ipld.EXPR k, .number 9, n, b]
  | .proj n e     => .array #[.number $ Ipld.EXPR k, .number 10, n, e]

def constToIpld : (Ipld.Const k) → Ipld
  | .axiom ⟨n, l, t, s⟩                 => .array #[.number $ Ipld.CONST k, .number 0,  n, l, t, s]
  | .theorem ⟨n, l, t, v⟩               => .array #[.number $ Ipld.CONST k, .number 1,  n, l, t, v]
  | .opaque ⟨n, l, t, v, s⟩             => .array #[.number $ Ipld.CONST k, .number 2,  n, l, t, v, s]
  | .quotient ⟨n, l, t, K⟩              => .array #[.number $ Ipld.CONST k, .number 3,  n, l, t, K]
  | .definition ⟨n, l, t, v, s⟩         => .array #[.number $ Ipld.CONST k, .number 4,  n, l, t, v, s]
  | .inductiveProj ⟨n, l, t, b, i⟩      => .array #[.number $ Ipld.CONST k, .number 5, n, l, t, b, i]
  | .constructorProj ⟨n, l, t, b, i, j⟩ => .array #[.number $ Ipld.CONST k, .number 6, n, l, t, b, i, j]
  | .recursorProj ⟨n, l, t, b, i, j⟩    => .array #[.number $ Ipld.CONST k, .number 7, n, l, t, b, i, j]
  | .definitionProj ⟨n, l, t, b, i⟩     => .array #[.number $ Ipld.CONST k, .number 8, n, l, t, b, i]
  | .mutDefBlock ds                    => .array #[.number $ Ipld.CONST k, .number 9,  ds]
  | .mutIndBlock is                    => .array #[.number $ Ipld.CONST k, .number 10, is]

def univToCid (univ : Ipld.Univ k) : Ipld.UnivCid k :=
  { data := ipldToCid (Ipld.UNIV k).toNat (univToIpld univ) }

def exprToCid (expr : Ipld.Expr k) : Ipld.ExprCid k :=
  { data := ipldToCid (Ipld.EXPR k).toNat (exprToIpld expr) }

def constToCid (const : Ipld.Const k) : Ipld.ConstCid k :=
  { data := ipldToCid (Ipld.CONST k).toNat (constToIpld const) }

end ToIpld
end Yatima
