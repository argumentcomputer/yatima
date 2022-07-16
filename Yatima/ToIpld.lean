import Ipld.Cid
import Ipld.Ipld
import Ipld.DagCbor
import Ipld.Multihash
import Yatima.Univ
import Yatima.Expr
import Yatima.Const

namespace Yatima.ToIpld

def ipldToCid (codec: Nat) (ipld : Ipld): Cid :=
  let cbor := DagCbor.serialize ipld;
  let hash := Multihash.sha3_256 cbor;
  { version := 0x01, codec, hash }

instance : Coe Nat Ipld where
  coe x := .bytes x.toByteArrayBE

instance : Coe Bool Ipld where
  coe x := .bool x

instance : Coe Name Ipld where
  coe x := .string x

instance : Coe (UnivCid .Anon)  Ipld where coe u := .link u.data
instance : Coe (UnivCid .Meta)  Ipld where coe u := .link u.data
instance : Coe (ExprCid .Anon)  Ipld where coe u := .link u.data
instance : Coe (ExprCid .Meta)  Ipld where coe u := .link u.data
instance : Coe (ConstCid .Anon) Ipld where coe u := .link u.data
instance : Coe (ConstCid .Meta) Ipld where coe u := .link u.data

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

instance : Coe Unit Ipld where coe
  | .unit => .array #[]

instance : Coe (RecursorRule .Anon) Ipld where coe
  | .mk c f r => .array #[c, f, r]

instance : Coe (RecursorRule .Meta) Ipld where coe
  | .mk c r => .array #[c, r]

instance : Coe (Recursor .Anon b) Ipld where coe
  | .mk l t p i m m' rs k => .array #[l, t, p, i, m, m', match b with | .true => rs | .false => rs, k]

instance : Coe (Sigma (Recursor .Anon)) Ipld where coe
  | .mk b (.mk l t p i m m' rs k) => .array #[l, t, p, i, m, m', match b with | .true => rs | .false => rs, k]

instance : Coe (Recursor .Meta b) Ipld where coe
  | .mk n l t rs => .array #[n, l, t, match b with | .true => rs | .false => rs]

instance : Coe (Sigma (Recursor .Meta)) Ipld where coe
  | .mk b (.mk n l t rs) => .array #[b, n, l, t, match b with | .true => rs | .false => rs]

instance : Coe (Constructor .Anon) Ipld where coe
  | .mk t l p f r => .array #[t, l, p, f, r]

instance : Coe (Constructor .Meta) Ipld where coe
  | .mk n l t r => .array #[n, l, t, r]

instance : Coe (Inductive .Anon) Ipld where coe
  | .mk l t p i cs rs r s r' => .array #[l, t, p, i, cs, rs, r, s, r']

instance : Coe (Inductive .Meta) Ipld where coe
  | .mk n l t cs rs => .array #[n, l, t, cs, rs]

instance : Coe QuotKind Ipld where coe
  | .type => .number 0
  | .ctor => .number 1
  | .lift => .number 3
  | .ind  => .number 4

instance : Coe (Definition .Anon) Ipld where coe
  | .mk n l t v => .array #[n, l, t, v]

instance : Coe (Definition .Meta) Ipld where coe
  | .mk n l t v => .array #[n, l, t, v]

def univAnonToIpld : (Univ .Anon) → Ipld
  | .zero     => .array #[.number UNIVANON, .number 0]
  | .succ p   => .array #[.number UNIVANON, .number 1, p]
  | .max a b  => .array #[.number UNIVANON, .number 2, a, b]
  | .imax a b => .array #[.number UNIVANON, .number 3, a, b]
  | .param _ (i : Nat)  => .array #[.number UNIVANON, .number 4, i]

def univMetaToIpld : (Univ .Meta) → Ipld
  | .zero     => .array #[.number UNIVMETA, .number 0]
  | .succ p   => .array #[.number UNIVMETA, .number 1, p]
  | .max a b  => .array #[.number UNIVMETA, .number 2, a, b]
  | .imax a b => .array #[.number UNIVMETA, .number 3, a, b]
  | .param (n : Name) _  => .array #[.number UNIVMETA, .number 4, n]

def exprAnonToIpld : (Expr .Anon) → Ipld
  | .var _ (i : Nat) => .array #[.number EXPRANON, .number 0, i]
  | .sort u     => .array #[.number EXPRANON, .number 1, u]
  | .const c ls => .array #[.number EXPRANON, .number 2, c, ls]
  | .app f a    => .array #[.number EXPRANON, .number 3, f, a]
  | .lam t b    => .array #[.number EXPRANON, .number 4, t, b]
  | .pi t b     => .array #[.number EXPRANON, .number 5, t, b]
  | .letE n t v => .array #[.number EXPRANON, .number 6, n, t, v]
  | .lit l      => .array #[.number EXPRANON, .number 7, l]
  | .lty l      => .array #[.number EXPRANON, .number 8, l]
  | .fix b      => .array #[.number EXPRANON, .number 9, b]
  | .proj n e   => .array #[.number EXPRANON, .number 10, n, e]

def exprMetaToIpld : (Expr .Meta) → Ipld
  | .var (i : Name) _ => .array #[.number EXPRMETA, .number 0, i]
  | .sort u     => .array #[.number EXPRMETA, .number 1, u]
  | .const (n : Name) c ls => .array #[.number EXPRMETA, .number 2, n, c, ls]
  | .app f a    => .array #[.number EXPRMETA, .number 3, f, a]
  | .lam t b    => .array #[.number EXPRMETA, .number 4, t, b]
  | .pi t b     => .array #[.number EXPRMETA, .number 5, t, b]
  | .letE n t v => .array #[.number EXPRMETA, .number 6, n, t, v]
  | .lit l      => .array #[.number EXPRMETA, .number 7, l]
  | .lty l      => .array #[.number EXPRMETA, .number 8, l]
  | .fix b      => .array #[.number EXPRMETA, .number 9, b]
  | .proj n e   => .array #[.number EXPRMETA, .number 10, n, e]

def constAnonToIpld : (Const .Anon) → Ipld
  | .axiom ⟨l, t, s⟩         => .array #[.number CONSTANON, .number 0,  l, t, s]
  | .theorem ⟨l, t, v⟩       => .array #[.number CONSTANON, .number 1,  l, t, v]
  | .opaque ⟨l, t, v, s⟩     => .array #[.number CONSTANON, .number 2,  l, t, v, s]
  | .quotient ⟨l, t, k⟩      => .array #[.number CONSTANON, .number 3,  l, t, k]
  | .definition ⟨n, l, t, v⟩ => .array #[.number CONSTANON, .number 4,  n, l, t, v]
  | .inductiveProj ⟨l, t, b, i⟩       => .array #[.number CONSTANON, .number 5,  l, t, b, i]
  | .constructorProj ⟨l, t, b, i, j⟩  => .array #[.number CONSTANON, .number 6,  l, t, b, i, j]
  | .recursorProj ⟨l, t, b, i, j⟩ => .array #[.number CONSTANON, .number 7,  l, t, b, i, j]
  | .definitionProj ⟨l, t, b, i⟩      => .array #[.number CONSTANON, .number 8,  l, t, b, i]
  | .mutDefBlock ds => .array #[.number CONSTANON, .number 9,  ds]
  | .mutIndBlock is => .array #[.number CONSTANON, .number 10, is]

def constMetaToIpld : (Const .Meta) → Ipld
  | .axiom ⟨n, l, t⟩         => .array #[.number CONSTMETA, .number 0,  n, l, t]
  | .theorem ⟨n, l, t, v⟩    => .array #[.number CONSTMETA, .number 1,  n, l, t, v]
  | .opaque ⟨n, l, t, v⟩     => .array #[.number CONSTMETA, .number 2,  n, l, t, v]
  | .quotient ⟨n, l, t⟩      => .array #[.number CONSTMETA, .number 3,  n, l, t]
  | .definition ⟨n, l, t, v⟩ => .array #[.number CONSTMETA, .number 4,  n, l, t, v]
  | .inductiveProj ⟨n, l, t, b⟩   => .array #[.number CONSTMETA, .number 5,  n, l, t, b]
  | .constructorProj ⟨n, l, t, b⟩ => .array #[.number CONSTMETA, .number 6,  n, l, t, b]
  | .recursorProj ⟨n, l, t, b⟩    => .array #[.number CONSTMETA, .number 7,  n, l, t, b]
  | .definitionProj ⟨n, l, t, b⟩  => .array #[.number CONSTMETA, .number 8,  n, l, t, b]
  | .mutDefBlock ds => .array #[.number CONSTMETA, .number 9,  ds]
  | .mutIndBlock is => .array #[.number CONSTMETA, .number 10, is]

def univAnonToCid (univAnon : Univ .Anon) : UnivCid .Anon :=
  { data := ipldToCid UNIVANON.toNat (univAnonToIpld univAnon) }

def univMetaToCid (univMeta : Univ .Meta) : UnivCid .Meta :=
  { data := ipldToCid UNIVMETA.toNat (univMetaToIpld univMeta) }

def exprAnonToCid (exprAnon : Expr .Anon) : ExprCid .Anon :=
  { data := ipldToCid EXPRANON.toNat (exprAnonToIpld exprAnon) }

def exprMetaToCid (exprMeta : Expr .Meta) : ExprCid .Meta :=
  { data := ipldToCid EXPRMETA.toNat (exprMetaToIpld exprMeta) }

def constAnonToCid (constAnon : Const .Anon) : ConstCid .Anon :=
  { data := ipldToCid CONSTANON.toNat (constAnonToIpld constAnon) }

def constMetaToCid (constMeta : Const .Meta) : ConstCid .Meta :=
  { data := ipldToCid CONSTMETA.toNat (constMetaToIpld constMeta) }

end Yatima.ToIpld
