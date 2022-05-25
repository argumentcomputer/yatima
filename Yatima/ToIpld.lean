import Yatima.Ipld.Cid
import Yatima.Ipld.Ipld
import Yatima.Ipld.DagCbor
import Yatima.Ipld.Multihash
import Yatima.Univ
import Yatima.Expr
import Yatima.Const

namespace Yatima.ToIpld

def ipldToCid (ipld : Ipld) : Except String Cid :=
  match Cid.fromBytes (Multihash.sha3_256 (DagCbor.serialize ipld)).digest with
  | none     => throw "Unable to generate Cid for {-- todo}"
  | some cid => return cid

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

def exprMetaToIpld : ExprMeta → Ipld
  | .var n        => .array #[.number EXPRMETA, .number 0, n]
  | .sort u       => .array #[.number EXPRMETA, .number 1, u]
  | .const n c ls => .array #[.number EXPRMETA, .number 2, n, c, ls]
  | .app f a      => .array #[.number EXPRMETA, .number 3, f, a]
  | .lam i n t b  => .array #[.number EXPRMETA, .number 4, i, n, t, b]
  | .pi i n t b   => .array #[.number EXPRMETA, .number 5, i, n, t, b]
  | .letE n t v   => .array #[.number EXPRMETA, .number 6, n, t, v]
  | .lit l        => .array #[.number EXPRMETA, .number 7, l]
  | .lty l        => .array #[.number EXPRMETA, .number 8, l]
  | .fix n b      => .array #[.number EXPRMETA, .number 9, n, b]

instance : Coe AxiomAnon (Array Ipld) where coe
  | .mk l t s  => #[l, t, s]

instance : Coe AxiomMeta (Array Ipld) where coe
  | .mk n l t => #[n, l, t]

instance : Coe TheoremAnon (Array Ipld) where coe
  | .mk l t v => #[l, t, v]

instance : Coe TheoremMeta (Array Ipld) where coe
  | .mk n l t v => #[n, l, t, v]

instance : Coe OpaqueAnon (Array Ipld) where coe
  | .mk l t v s => #[l, t, v, s]

instance : Coe OpaqueMeta (Array Ipld) where coe
  | .mk n l t v => #[n, l, t, v]

def definitionSafetyToIpld : DefinitionSafety -> Ipld
  | .safe    => .number 0
  | .unsafe  => .number 1
  | .partial => .number 2

instance : Coe DefinitionAnon (Array Ipld) where coe
  | .mk l t v s => #[l, t, v, definitionSafetyToIpld s]

instance : Coe DefinitionMeta (Array Ipld) where coe
  | .mk n l t v => #[n, l, t, v]

instance : Coe InductiveAnon (Array Ipld) where coe
  | .mk l t p i c r s rf n => #[l, t, p, i, c, r, s, rf, n]

instance : Coe InductiveMeta (Array Ipld) where coe
  | .mk n l t c => #[n, l, t, c]

instance : Coe ConstructorAnon (Array Ipld) where coe
  | .mk l t i idx p f s => #[l, t, i, idx, p, f, s]

instance : Coe ConstructorMeta (Array Ipld) where coe
  | .mk n l t i => #[n, l, t, i]

-- internal fields, so no extra type-identifying constants needed
instance : Coe RecursorRuleAnon Ipld where coe
  | .mk c f r => .array #[c, f, r]

instance : Coe RecursorRuleMeta Ipld where coe
  | .mk c r => .array #[c, r]

instance : Coe RecursorAnon (Array Ipld) where coe
  | .mk l t i p is m mi r k s => #[l, t, i, p, is, m, mi, r, k, s]

instance : Coe RecursorMeta (Array Ipld) where coe
  | .mk n l t i r => #[n, l, t, i, r]

def quotKindToIpld : QuotKind -> Ipld
  | .type => .number 0
  | .ctor => .number 1
  | .lift => .number 3
  | .ind  => .number 4

instance : Coe QuotientAnon (Array Ipld) where coe
  | .mk l t k => #[l, t, quotKindToIpld k]

instance : Coe QuotientMeta (Array Ipld) where coe
  | .mk n l t => #[n, l, t]

def constAnonToIpld : ConstAnon → Ipld
  | .axiom a       => .array $ (#[.number CONSTANON, .number 0]).append a
  | .theorem t     => .array $ (#[.number CONSTANON, .number 1]).append t
  | .inductive i   => .array $ (#[.number CONSTANON, .number 2]).append i
  | .opaque o      => .array $ (#[.number CONSTANON, .number 3]).append o
  | .definition d  => .array $ (#[.number CONSTANON, .number 4]).append d
  | .constructor c => .array $ (#[.number CONSTANON, .number 5]).append c
  | .recursor r    => .array $ (#[.number CONSTANON, .number 6]).append r
  | .quotient q    => .array $ (#[.number CONSTANON, .number 7]).append q

def constMetaToIpld : ConstMeta → Ipld
  | .axiom a       => .array $ (#[.number CONSTMETA, .number 0]).append a
  | .theorem t     => .array $ (#[.number CONSTMETA, .number 1]).append t
  | .inductive i   => .array $ (#[.number CONSTMETA, .number 2]).append i
  | .opaque o      => .array $ (#[.number CONSTMETA, .number 3]).append o
  | .definition d  => .array $ (#[.number CONSTMETA, .number 4]).append d
  | .constructor c => .array $ (#[.number CONSTMETA, .number 5]).append c
  | .recursor r    => .array $ (#[.number CONSTMETA, .number 6]).append r
  | .quotient q    => .array $ (#[.number CONSTMETA, .number 7]).append q

def univAnonToCid (univAnon : UnivAnon) : Except String UnivAnonCid :=
  match ipldToCid $ univAnonToIpld univAnon with
  | .ok    cid => return ⟨cid⟩
  | .error msg => throw msg

def univMetaToCid (univMeta : UnivMeta) : Except String UnivMetaCid :=
  match ipldToCid $ univMetaToIpld univMeta with
  | .ok    cid => return ⟨cid⟩
  | .error msg => throw msg

def exprAnonToCid (exprAnon : ExprAnon) : Except String ExprAnonCid :=
  match ipldToCid $ exprAnonToIpld exprAnon with
  | .ok    cid => return ⟨cid⟩
  | .error msg => throw msg

def exprMetaToCid (exprMeta : ExprMeta) : Except String ExprMetaCid :=
  match ipldToCid $ exprMetaToIpld exprMeta with
  | .ok    cid => return ⟨cid⟩
  | .error msg => throw msg

def constAnonToCid (constAnon : ConstAnon) : Except String ConstAnonCid :=
  match ipldToCid $ constAnonToIpld constAnon with
  | .ok    cid => return ⟨cid⟩
  | .error msg => throw msg

def constMetaToCid (constMeta : ConstMeta) : Except String ConstMetaCid :=
  match ipldToCid $ constMetaToIpld constMeta with
  | .ok    cid => return ⟨cid⟩
  | .error msg => throw msg

end Yatima.ToIpld
