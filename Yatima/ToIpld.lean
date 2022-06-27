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

instance : Coe UnivAnonCid  Ipld where coe u := .link u.data
instance : Coe UnivMetaCid  Ipld where coe u := .link u.data
instance : Coe ExprAnonCid  Ipld where coe u := .link u.data
instance : Coe ExprMetaCid  Ipld where coe u := .link u.data
instance : Coe ConstAnonCid Ipld where coe u := .link u.data
instance : Coe ConstMetaCid Ipld where coe u := .link u.data

instance (α : Type) [Coe α Ipld] : Coe (List α) Ipld where
  coe l := .array ⟨List.map (fun (x : α) => x) l⟩

instance (α β : Type) [Coe α Ipld] [Coe β Ipld] : Coe (α × β) Ipld where
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

instance : Coe ExternalRecursorRuleAnon Ipld where coe
  | .mk c f r => .array #[c, f, r]

instance : Coe ExternalRecursorRuleMeta Ipld where coe
  | .mk c r => .array #[c, r]

instance : Coe ExternalRecursorInfoAnon Ipld where coe
  | .mk t p i m m' rs k => .array #[t, p, i, m, m', rs, k]

instance : Coe ExternalRecursorInfoMeta Ipld where coe
  | .mk n t rs => .array #[n, t, rs]

instance : Coe InternalRecursorRuleAnon Ipld where coe
  | .mk c f r => .array #[c, f, r]

instance : Coe InternalRecursorRuleMeta Ipld where coe
  | .mk r => .array #[r]

instance : Coe InternalRecursorInfoAnon Ipld where coe
  | .mk t p i m m' rs k => .array #[t, p, i, m, m', rs, k]

instance : Coe InternalRecursorInfoMeta Ipld where coe
  | .mk n t rs => .array #[n, t, rs]

instance : Coe ConstructorInfoAnon Ipld where coe
  | .mk t p f => .array #[t, p, f]

instance : Coe ConstructorInfoMeta Ipld where coe
  | .mk n t => .array #[n, t]

instance : Coe InductiveInfoAnon Ipld where coe
  | .mk l t p i cs is es r s r' => .array #[l, t, p, i, cs, is, es, r, s, r']

instance : Coe InductiveInfoMeta Ipld where coe
  | .mk n l t cs is es => .array #[n, l, t, cs, is, es]

instance : Coe QuotKind Ipld where coe
  | .type => .number 0
  | .ctor => .number 1
  | .lift => .number 3
  | .ind  => .number 4

instance : Coe DefinitionAnon Ipld where coe
  | .mk n l t v => .array #[n, l, t, v]

instance : Coe DefinitionMeta Ipld where coe
  | .mk n l t v => .array #[n, l, t, v]

def univAnonToIpld : UnivAnon → Ipld
  | .zero     => .array #[.number UNIVANON, .number 0]
  | .succ p   => .array #[.number UNIVANON, .number 1, p]
  | .max a b  => .array #[.number UNIVANON, .number 2, a, b]
  | .imax a b => .array #[.number UNIVANON, .number 3, a, b]
  | .param n  => .array #[.number UNIVANON, .number 4, n]

def univMetaToIpld : UnivMeta → Ipld
  | .zero     => .array #[.number UNIVMETA, .number 0]
  | .succ p   => .array #[.number UNIVMETA, .number 1, p]
  | .max a b  => .array #[.number UNIVMETA, .number 2, a, b]
  | .imax a b => .array #[.number UNIVMETA, .number 3, a, b]
  | .param n  => .array #[.number UNIVMETA, .number 4, n]

def exprAnonToIpld : ExprAnon → Ipld
  | .var n      => .array #[.number EXPRANON, .number 0, n]
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

def exprMetaToIpld : ExprMeta → Ipld
  | .var n        => .array #[.number EXPRMETA, .number 0, n]
  | .sort u       => .array #[.number EXPRMETA, .number 1, u]
  | .const n c ls => .array #[.number EXPRMETA, .number 2, n, c, ls]
  | .app f a      => .array #[.number EXPRMETA, .number 3, f, a]
  | .lam i n t b  => .array #[.number EXPRMETA, .number 4, i, n, t, b]
  | .pi i n t b   => .array #[.number EXPRMETA, .number 5, i, n, t, b]
  | .letE n t v b => .array #[.number EXPRMETA, .number 6, n, t, v, b]
  | .lit          => .array #[.number EXPRMETA, .number 7]
  | .lty          => .array #[.number EXPRMETA, .number 8]
  | .fix n b      => .array #[.number EXPRMETA, .number 9, n, b]
  | .proj n e     => .array #[.number EXPRANON, .number 10, n, e]

def constAnonToIpld : ConstAnon → Ipld
  | .axiom ⟨l, t, s⟩              => .array #[.number CONSTANON, .number 0, l, t, s]
  | .theorem ⟨l, t, v⟩            => .array #[.number CONSTANON, .number 1, l, t, v]
  | .opaque ⟨l, t, v, s⟩          => .array #[.number CONSTANON, .number 2, l, t, v, s]
  | .definition ⟨n, l, t, v⟩      => .array #[.number CONSTANON, .number 3, n, l, t, v]
  | .indBlock is                  => .array #[.number CONSTANON, .number 4, is]
  | .inductive ⟨l, t, b, i⟩       => .array #[.number CONSTANON, .number 5, l, t, b, i]
  | .constructor ⟨l, t, b, i, j⟩  => .array #[.number CONSTANON, .number 6, l, t, b, i, j]
  | .recursor ⟨l, t, b, i, j, i'⟩ => .array #[.number CONSTANON, .number 7, l, t, b, i, j, i']
  | .quotient ⟨l, t, k⟩           => .array #[.number CONSTANON, .number 8, l, t, k]
  | .mutDefBlock ds               => .array #[.number CONSTANON, .number 9, ds]
  | .mutDef ⟨l, t, b, i⟩          => .array #[.number CONSTANON, .number 10, l, t, b, i]

def constMetaToIpld : ConstMeta → Ipld
  | .axiom ⟨n, l, t⟩          => .array #[.number CONSTMETA, .number 0, n, l, t]
  | .theorem ⟨n, l, t, v⟩     => .array #[.number CONSTMETA, .number 1, n, l, t, v]
  | .opaque ⟨n, l, t, v⟩      => .array #[.number CONSTMETA, .number 2, n, l, t, v]
  | .definition ⟨n, l, t, v⟩  => .array #[.number CONSTMETA, .number 3, n, l, t, v]
  | .indBlock is              => .array #[.number CONSTMETA, .number 4, is]
  | .inductive ⟨n, l, t, b⟩   => .array #[.number CONSTMETA, .number 5, n, l, t, b]
  | .constructor ⟨n, l, t, b⟩ => .array #[.number CONSTMETA, .number 6, n, l, t, b]
  | .recursor ⟨n, l, t, b⟩    => .array #[.number CONSTMETA, .number 7, n, l, t, b]
  | .quotient ⟨n, l, t⟩       => .array #[.number CONSTMETA, .number 8, n, l, t]
  | .mutDefBlock ds           => .array #[.number CONSTMETA, .number 9, ds]
  | .mutDef ⟨n, l, t, b⟩      => .array #[.number CONSTMETA, .number 10, n, l, t, b]

def univAnonToCid (univAnon : UnivAnon) : UnivAnonCid :=
  { data := ipldToCid UNIVANON.toNat (univAnonToIpld univAnon) }

def univMetaToCid (univMeta : UnivMeta) : UnivMetaCid :=
  { data := ipldToCid UNIVMETA.toNat (univMetaToIpld univMeta) }

def exprAnonToCid (exprAnon : ExprAnon) : ExprAnonCid :=
  { data := ipldToCid EXPRANON.toNat (exprAnonToIpld exprAnon) }

def exprMetaToCid (exprMeta : ExprMeta) : ExprMetaCid :=
  { data := ipldToCid EXPRMETA.toNat (exprMetaToIpld exprMeta) }

def constAnonToCid (constAnon : ConstAnon) : ConstAnonCid :=
  { data := ipldToCid CONSTANON.toNat (constAnonToIpld constAnon) }

def constMetaToCid (constMeta : ConstMeta) : ConstMetaCid :=
  { data := ipldToCid CONSTMETA.toNat (constMetaToIpld constMeta) }

end Yatima.ToIpld
