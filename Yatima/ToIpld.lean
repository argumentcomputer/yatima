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
  | .lit          => .array #[.number EXPRMETA, .number 7]
  | .lty          => .array #[.number EXPRMETA, .number 8]
  | .fix n b      => .array #[.number EXPRMETA, .number 9, n, b]

def axiomAnonToIpld : AxiomAnon → Ipld
  | .mk l t s  => .array #[.number AXIOMANON, .number 0, l, t, s]

def axiomMetaToIpld : AxiomMeta → Ipld
  | .mk n l t => .array #[.number AXIOMMETA, .number 0, n, l, t]

def theoremAnonToIpld : TheoremAnon → Ipld
  | .mk l t v => .array #[.number THEOREMANON, .number 0, l, t, v]

def theoremMetaToIpld : TheoremMeta -> Ipld
  | .mk n l t v => .array #[.number THEOREMMETA, .number 0, n, l, t, v]

def opaqueAnonToIpld : OpaqueAnon -> Ipld
  | .mk l t v s => .array #[.number OPAQUEANON, .number 0, l, t, v, s]

def opaqueMetaToIpld : OpaqueMeta -> Ipld
  | .mk n l t v => .array #[.number OPAQUEMETA, .number 0, n, l, t, v]

def definitionSafetyToIpld : DefinitionSafety -> Ipld
  | .safe      => .array #[.number DEFINITIONSAFETY, .number 0]
  | .«unsafe»  => .array #[.number DEFINITIONSAFETY, .number 1]
  | .«partial» => .array #[.number DEFINITIONSAFETY, .number 2]

def definitionAnonToIpld : DefinitionAnon -> Ipld
  | .mk l t v s => .array #[.number DEFINITIONANON, .number 0, l, t, v, definitionSafetyToIpld s]

def definitionMetaToIpld : DefinitionMeta -> Ipld
  | .mk n l t v => .array #[.number DEFINITIONMETA, .number 0, n, l, t, v]

def inductiveAnonToIpld : InductiveAnon -> Ipld
  | .mk l t p i c r s rf n => .array #[.number INDUCTIVEANON, .number 0, l, t, p, i, c, r, s, rf, n]

def inductiveMetaToIpld : InductiveMeta -> Ipld
  | .mk n l t c => .array #[.number INDUCTIVEMETA, .number 0, n, l, t, c]

def constructorAnonToIpld : ConstructorAnon -> Ipld
  | .mk l t i idx p f s => .array #[.number CONSTRUCTORANON, .number 0, l, t, i, idx, p, f, s]

def constructorMetaToIpld : ConstructorMeta -> Ipld
  | .mk n l t i => .array #[.number CONSTRUCTORMETA, .number 0, n, l, t, i]

def recursorRuleAnonToIpld : RecursorRuleAnon -> Ipld
  | .mk c f r => .array #[.number RECURSORRULEANON, .number 0, c, f, r]

instance : Coe RecursorRuleAnon Ipld where coe r := recursorRuleAnonToIpld r

def recursorRuleMetaToIpld : RecursorRuleMeta -> Ipld
  | .mk c r => .array #[.number RECURSORRULEMETA, .number 0, c, r]

instance : Coe RecursorRuleMeta Ipld where coe r := recursorRuleMetaToIpld r

def recursorAnonToIpld : RecursorAnon -> Ipld
  | .mk l t i p is m mi r k s => .array #[.number RECURSORANON, .number 0, l, t, i, p, is, m, mi, r, k, s]

def recursorMetaToIpld : RecursorMeta -> Ipld
  | .mk n l t i r => .array #[.number RECURSORMETA, .number 0, n, l, t, i, r]

def quotKindToIpld : QuotKind -> Ipld
  | .type      => .array #[.number QUOTKIND, .number 0]
  | .ctor      => .array #[.number QUOTKIND, .number 1]
  | .lift      => .array #[.number QUOTKIND, .number 3]
  | .ind       => .array #[.number QUOTKIND, .number 4]

def quotientAnonToIpld : QuotientAnon -> Ipld
  | .mk l t k => .array #[.number QUOTIENTANON, .number 0, l, t, quotKindToIpld k]

def quotientMetaToIpld : QuotientMeta -> Ipld
  | .mk n l t => .array #[.number QUOTIENTMETA, .number 0, n, l, t]

def constAnonToIpld : ConstAnon → Ipld
  | .«axiom» a     => .array #[.number CONSTANON, .number 0, axiomAnonToIpld a]
  | .«theorem» t   => .array #[.number CONSTANON, .number 1, theoremAnonToIpld t]
  | .«inductive» i => .array #[.number CONSTANON, .number 2, inductiveAnonToIpld i]
  | .opaque o      => .array #[.number CONSTANON, .number 3, opaqueAnonToIpld o]
  | .definition d  => .array #[.number CONSTANON, .number 4, definitionAnonToIpld d]
  | .constructor c => .array #[.number CONSTANON, .number 5, constructorAnonToIpld c]
  | .recursor r    => .array #[.number CONSTANON, .number 6, recursorAnonToIpld r]
  | .quotient q    => .array #[.number CONSTANON, .number 7, quotientAnonToIpld q]

def constMetaToIpld : ConstMeta → Ipld
  | .«axiom» a     => .array #[.number CONSTMETA, .number 0, axiomMetaToIpld a]
  | .«theorem» t   => .array #[.number CONSTMETA, .number 1, theoremMetaToIpld t]
  | .«inductive» i => .array #[.number CONSTMETA, .number 2, inductiveMetaToIpld i]
  | .opaque o      => .array #[.number CONSTMETA, .number 3, opaqueMetaToIpld o]
  | .definition d  => .array #[.number CONSTMETA, .number 4, definitionMetaToIpld d]
  | .constructor c => .array #[.number CONSTMETA, .number 5, constructorMetaToIpld c]
  | .recursor r    => .array #[.number CONSTMETA, .number 6, recursorMetaToIpld r]
  | .quotient q    => .array #[.number CONSTMETA, .number 7, quotientMetaToIpld q]

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
