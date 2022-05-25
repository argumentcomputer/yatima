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

instance : Coe Name Ipld where
  coe x := .string x

instance : Coe UnivAnonCid  Ipld where coe u := .link u.data
instance : Coe UnivMetaCid  Ipld where coe u := .link u.data
instance : Coe ExprAnonCid  Ipld where coe u := .link u.data
instance : Coe ExprMetaCid  Ipld where coe u := .link u.data
instance : Coe ConstAnonCid Ipld where coe u := .link u.data
instance : Coe ConstMetaCid Ipld where coe u := .link u.data

instance : Coe (List UnivAnonCid) Ipld where
  coe l := .array ⟨l.map (.link ·.data)⟩

instance : Coe (List UnivMetaCid) Ipld where
  coe l := .array ⟨l.map (.link ·.data)⟩

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
  | .var nam    => .array #[.number EXPRMETA, .number 0, nam]
  | .sort u     => .array #[.number EXPRMETA, .number 1, u]
  | .const c ls => .array #[.number EXPRMETA, .number 2, c, ls]
  | .app f a    => .array #[.number EXPRMETA, .number 3, f, a]
  | .lam t b    => .array #[.number EXPRMETA, .number 4, t, b]
  | .pi t b     => .array #[.number EXPRMETA, .number 5, t, b]
  | .letE n t v => .array #[.number EXPRMETA, .number 6, n, t, v]
  | .lit l      => .array #[.number EXPRMETA, .number 7, l]
  | .lty l      => .array #[.number EXPRMETA, .number 8, l]
  | .fix b      => .array #[.number EXPRMETA, .number 9, b]

def exprMetaToIpld : ExprMeta → Ipld
  | .var nam      => .array #[.number EXPRMETA, .number 0, nam]
  | .sort u       => .array #[.number EXPRMETA, .number 1, u]
  | .const n c ls => .array #[.number EXPRMETA, .number 2, n, c, ls]
  | .app f a      => .array #[.number EXPRMETA, .number 3, f, a]
  | .lam i n t b  => .array #[.number EXPRMETA, .number 4, i, n, t, b]
  | .pi i n t b   => .array #[.number EXPRMETA, .number 5, i, n, t, b]
  | .letE n t v   => .array #[.number EXPRMETA, .number 6, n, t, v]
  | .lit          => .array #[.number EXPRMETA, .number 7]
  | .lty          => .array #[.number EXPRMETA, .number 8]
  | .fix n b      => .array #[.number EXPRMETA, .number 9, n, b]

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

def constAnonToCid (constAnon : ConstAnon) : Except String ConstAnonCid := sorry
def constMetaToCid (constMeta : ConstMeta) : Except String ConstMetaCid := sorry

end Yatima.ToIpld
