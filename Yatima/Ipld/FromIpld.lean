import Ipld.Ipld
import Yatima.Datatypes.Store

namespace Yatima.Ipld

def listFromIpld (f : Ipld → Option α) : Ipld → Option (List α)
  | .array xs => xs.data.mapM f
  | _ => none

def optionFromIpld (f : Ipld → Option α) : Ipld → Option (Option α)
  | .null => some none
  | x => do
    let x ← f x
    pure $ some x

def natFromIpld : Ipld → Option Nat
  | .bytes b => return Nat.fromByteListBE b.data.data
  | _ => none

def nat?FromIpld : Ipld → Option (Option Nat)
  | .bytes b => return some $ Nat.fromByteListBE b.data.data
  | .null => return none
  | _ => none

def nameFromIpld : Ipld → Option Name
  | .array ar => ar.foldlM (init := .anonymous) fun acc i =>
    match i with
    | .bytes  b => pure $ acc.mkNum (Nat.fromByteListBE b.data.data)
    | .string s => pure $ acc.mkStr s
    | _ => none
  | _ => none

def binderInfoFromIpld : Ipld → Option BinderInfo
  | .number 0 => return .default
  | .number 1 => return .implicit
  | .number 2 => return .strictImplicit
  | .number 3 => return .instImplicit
  | _ => none

def quotKindFromIpld : Ipld → Option QuotKind
  | .number 0 => return .type
  | .number 1 => return .ctor
  | .number 2 => return .lift
  | .number 3 => return .ind
  | _ => none

def definitionSafetyFromIpld : Ipld → Option DefinitionSafety
  | .number 0 => return .safe
  | .number 1 => return .unsafe
  | .number 2 => return .partial
  | _ => none

def literalFromIpld : Ipld → Option Literal
  | .string s => return .strVal s
  | .bytes  b => return .natVal $ Nat.fromByteListBE b.data.data
  | _ => none

open IR

def splitNatₐFromIpld : (k : Kind) → Ipld → Option (Natₐ k)
  | .anon, .array #[.number 0, x] => return .injₗ (← natFromIpld  x)
  | .meta, .array #[.number 1, .null] => return .injᵣ ()
  | _, _ => none

def splitBoolₐFromIpld : (k : Kind) → Ipld → Option (Boolₐ k)
  | .anon, .array #[.number 0, .bool b] => return .injₗ b
  | .meta, .array #[.number 1, .null] => return .injᵣ ()
  | _, _ => none

def splitNatₐNameₘFromIpld : (k : Kind) → Ipld → Option (NatₐNameₘ k)
  | .anon, .array #[.number 0, x] => return .injₗ (← natFromIpld  x)
  | .meta, .array #[.number 1, x] => return .injᵣ (← nameFromIpld x)
  | _, _ => none

def splitNat?ₘFromIpld : (k : Kind) → Ipld → Option (Nat?ₘ k)
  | .anon, .array #[.number 0, .null] => return .injₗ ()
  | .meta, .array #[.number 1, x] => return .injᵣ (← nat?FromIpld x)
  | _, _ => none

def splitNameₘFromIpld : (k : Kind) → Ipld → Option (Nameₘ k)
  | .anon, .array #[.number 0, .null] => return .injₗ ()
  | .meta, .array #[.number 1, x] => return .injᵣ (← nameFromIpld x)
  | _, _ => none

def splitNatₐListNameₘFromIpld : (k : Kind) → Ipld → Option (NatₐListNameₘ k)
  | .anon, .array #[.number 0, x] => return .injₗ (← natFromIpld x)
  | .meta, .array #[.number 1, x] => return .injᵣ (← listFromIpld nameFromIpld x)
  | _, _ => none

def splitBinderInfoₐFromIpld : (k : Kind) → Ipld → Option (BinderInfoₐ k)
  | .anon, .array #[.number 0, x] => return .injₗ (← binderInfoFromIpld x)
  | .meta, .array #[.number 1, .null] => return .injᵣ ()
  | _, _ => none

def splitLiteralUnitFromIpld : (k : Kind) → Ipld → Option (Split Literal Unit k)
  | .anon, .array #[.number 0, x] => return .injₗ (← literalFromIpld x)
  | .meta, .array #[.number 1, .null] => return .injᵣ ()
  | _, _ => none

def splitQuotKindFromIpld : (k : Kind) → Ipld → Option (Split QuotKind Unit k)
  | .anon, .array #[.number 0, x] => return .injₗ (← quotKindFromIpld x)
  | .meta, .array #[.number 1, .null] => return .injᵣ ()
  | _, _ => none

def splitDefinitionSafetyUnitFromIpld :
    (k : Kind) → Ipld → Option (Split DefinitionSafety Unit k)
  | .anon, .array #[.number 0, x] => return .injₗ (← definitionSafetyFromIpld x)
  | .meta, .array #[.number 1, .null] => return .injᵣ ()
  | _, _ => none

def univCidFromIpld : Ipld → Option (UnivCid k)
  | .link c => return ⟨c⟩
  | _ => none

def exprCidFromIpld : Ipld → Option (ExprCid k)
  | .link c => return ⟨c⟩
  | _ => none

def constCidFromIpld : Ipld → Option (ConstCid k)
  | .link c => return ⟨c⟩
  | _ => none

def definitionFromIpld : Ipld → Option (Definition k)
  | .array #[n, l, t, v, s] =>
    return ⟨← splitNameₘFromIpld k n, ← splitNatₐListNameₘFromIpld k l,
      ← exprCidFromIpld t, ← exprCidFromIpld v,
      ← splitDefinitionSafetyUnitFromIpld k s⟩
  | _ => none

def mutDefFromIpld :
    (k : Kind) → Ipld → Option (Split (Definition k) (List (Definition k)) k)
  | .anon, .array #[.number 0, x] => return .injₗ (← definitionFromIpld x)
  | .meta, .array #[.number 1, x] => return .injᵣ (← listFromIpld definitionFromIpld x)
  | _, _ => none

def mutDefBlockFromIpld :
    (k : Kind) → Ipld → Option (List (Split (Definition k) (List (Definition k)) k))
  | .anon, .array ar => ar.data.mapM $ mutDefFromIpld .anon
  | .meta, .array ar => ar.data.mapM $ mutDefFromIpld .meta
  | _, _ => none

def constructorFromIpld : Ipld → Option (Constructor k)
  | .array #[n, t, l, i, p, f, s] =>
    return ⟨← splitNameₘFromIpld k n, ← splitNatₐListNameₘFromIpld k t,
      ← exprCidFromIpld l, ← splitNatₐFromIpld k i, ← splitNatₐFromIpld k p,
      ← splitNatₐFromIpld k f, ← splitBoolₐFromIpld k s⟩
  | _ => none

def recursorRuleFromIpld : Ipld → Option (RecursorRule k)
  | .array #[f, r] =>
    return ⟨← splitNatₐFromIpld k f, ← exprCidFromIpld r⟩
  | _ => none

def recursorFromIpld : Ipld → Option (Recursor k)
  | .array #[n, l, t, p, i, m, m', rs, k', e] => do
    return ⟨← splitNameₘFromIpld k n, ← splitNatₐListNameₘFromIpld k l, ← exprCidFromIpld t,
      ← splitNatₐFromIpld k p, ← splitNatₐFromIpld k i,
      ← splitNatₐFromIpld k m, ← splitNatₐFromIpld k m',
      ← listFromIpld recursorRuleFromIpld rs,
      ← splitBoolₐFromIpld k k',
      ← optionFromIpld constCidFromIpld e
      ⟩
  | _ => none

def mutIndFromIpld : Ipld → Option (Inductive k)
  | .array #[n, l, t, p, i, cs, rs, r, s, r'] =>
    return ⟨← splitNameₘFromIpld k n, ← splitNatₐListNameₘFromIpld k l,
      ← exprCidFromIpld t, ← splitNatₐFromIpld k p, ← splitNatₐFromIpld k i,
      ← listFromIpld constructorFromIpld cs,
      ← listFromIpld recursorFromIpld rs,
      ← splitBoolₐFromIpld k r, ← splitBoolₐFromIpld k s, ← splitBoolₐFromIpld k r'⟩
  | _ => none

def univAnonFromIpld : Ipld → Option (Univ .anon)
  | .array #[.number 0] =>
    return .zero
  | .array #[.number 1, p] =>
    return .succ (← univCidFromIpld p)
  | .array #[.number 2, a, b] =>
    return .max (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number 3, a, b] =>
    return .imax (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number 4, n] =>
    return .var (← splitNatₐNameₘFromIpld .anon n)
  | _ => none

def univMetaFromIpld : Ipld → Option (Univ .meta)
  | .array #[.number 0] => some .zero
  | .array #[.number 1, p] =>
    return .succ (← univCidFromIpld p)
  | .array #[.number 2, a, b] =>
    return .max (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number 3, a, b] =>
    return .imax (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number 4, n] =>
    return .var (← splitNatₐNameₘFromIpld .meta n)
  | _ => none

def exprAnonFromIpld : Ipld → Option (Expr .anon)
  | .array #[.number 0, n, i, ls] =>
    return .var (← splitNatₐNameₘFromIpld .anon n) (← splitNat?ₘFromIpld .anon i)
      (← listFromIpld univCidFromIpld ls)
  | .array #[.number 1, u] =>
    return .sort (← univCidFromIpld u)
  | .array #[.number 2, n, c, ls] =>
    return .const (← splitNameₘFromIpld .anon n) (← constCidFromIpld c)
      (← listFromIpld univCidFromIpld ls)
  | .array #[.number 3, f, a] =>
    return .app (← exprCidFromIpld f) (← exprCidFromIpld a)
  | .array #[.number 4, n, i, d, b] =>
    return .lam (← splitNameₘFromIpld .anon n) (← splitBinderInfoₐFromIpld .anon i)
      (← exprCidFromIpld d) (← exprCidFromIpld b)
  | .array #[.number 5, n, i, d, b] =>
    return .pi (← splitNameₘFromIpld .anon n) (← splitBinderInfoₐFromIpld .anon i)
      (← exprCidFromIpld d) (← exprCidFromIpld b)
  | .array #[.number 6, n, t, v, b] =>
    return .letE (← splitNameₘFromIpld .anon n) (← exprCidFromIpld t)
      (← exprCidFromIpld v) (← exprCidFromIpld b)
  | .array #[.number 7, l] =>
    return .lit (← splitLiteralUnitFromIpld .anon l)
  | .array #[.number 8, n, e] =>
    return .proj (← splitNatₐFromIpld .anon n) (← exprCidFromIpld e)
  | _ => none

def exprMetaFromIpld : Ipld → Option (Expr .meta)
  | .array #[.number 0, n, i, ls] =>
    return .var (← splitNatₐNameₘFromIpld .meta n) (← splitNat?ₘFromIpld .meta i)
      (← listFromIpld univCidFromIpld ls)
  | .array #[.number 1, u] =>
    return .sort (← univCidFromIpld u)
  | .array #[.number 2, n, c, ls] =>
    return .const (← splitNameₘFromIpld .meta n) (← constCidFromIpld c)
      (← listFromIpld univCidFromIpld ls)
  | .array #[.number 3, f, a] =>
    return .app (← exprCidFromIpld f) (← exprCidFromIpld a)
  | .array #[.number 4, n, i, d, b] =>
    return .lam (← splitNameₘFromIpld .meta n) (← splitBinderInfoₐFromIpld .meta i)
      (← exprCidFromIpld d) (← exprCidFromIpld b)
  | .array #[.number 5, n, i, d, b] =>
    return .pi (← splitNameₘFromIpld .meta n) (← splitBinderInfoₐFromIpld .meta i)
      (← exprCidFromIpld d) (← exprCidFromIpld b)
  | .array #[.number 6, n, t, v, b] =>
    return .letE (← splitNameₘFromIpld .meta n) (← exprCidFromIpld t)
      (← exprCidFromIpld v) (← exprCidFromIpld b)
  | .array #[.number 7, l] =>
    return .lit (← splitLiteralUnitFromIpld .meta l)
  | .array #[.number 8, n, e] =>
    return .proj (← splitNatₐFromIpld .meta n) (← exprCidFromIpld e)
  | _ => none

def constAnonFromIpld : Ipld → Option (Const .anon)
  | .array #[.number 0, n, l, t, s] =>
    return .axiom ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← splitBoolₐFromIpld .anon s⟩
  | .array #[.number 1, n, l, t, v] =>
    return .theorem ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← exprCidFromIpld v⟩
  | .array #[.number 2, n, l, t, v, s] =>
    return .opaque ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← exprCidFromIpld v, ← splitBoolₐFromIpld .anon s⟩
  | .array #[.number 3, n, l, t, k] =>
    return .quotient ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← splitQuotKindFromIpld .anon k⟩
  | .array #[.number 5, n, l, t, b, i] =>
    return .inductiveProj ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .anon i⟩
  | .array #[.number 6, n, l, t, b, i, j] =>
    return .constructorProj ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .anon i, ← splitNatₐFromIpld .anon j⟩
  | .array #[.number 7, n, l, t, b, i, j] =>
    return .recursorProj ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .anon i, ← splitNatₐFromIpld .anon j⟩
  | .array #[.number 8, n, l, t, b, i] =>
    return .definitionProj ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← natFromIpld i⟩
  | .array #[.number 9, b] =>
    return .mutDefBlock (← mutDefBlockFromIpld .anon b)
  | .array #[.number 10, b] =>
    return .mutIndBlock (← listFromIpld mutIndFromIpld b)
  | _ => none

def constMetaFromIpld : Ipld → Option (Const .meta)
  | .array #[.number 0, n, l, t, s] =>
    return .axiom ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← splitBoolₐFromIpld .meta s⟩
  | .array #[.number 1, n, l, t, v] =>
    return .theorem ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← exprCidFromIpld v⟩
  | .array #[.number 2, n, l, t, v, s] =>
    return .opaque ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← exprCidFromIpld v, ← splitBoolₐFromIpld .meta s⟩
  | .array #[.number 3, n, l, t, k] =>
    return .quotient ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← splitQuotKindFromIpld .meta k⟩
  | .array #[.number 5, n, l, t, b, i] =>
    return .inductiveProj ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .meta i⟩
  | .array #[.number 6, n, l, t, b, i, j] =>
    return .constructorProj ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .meta i, ← splitNatₐFromIpld .meta j⟩
  | .array #[.number 7, n, l, t, b, i, j] =>
    return .recursorProj ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .meta i, ← splitNatₐFromIpld .meta j⟩
  | .array #[.number 8, n, l, t, b, i] =>
    return .definitionProj ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← natFromIpld i⟩
  | .array #[.number 9, b] =>
    return .mutDefBlock (← mutDefBlockFromIpld .meta b)
  | .array #[.number 10, b] =>
    return .mutIndBlock (← listFromIpld mutIndFromIpld b)
  | _ => none

def constsTreeFromIpld (ar : Array Ipld) :
    Option (Std.RBSet (Both ConstCid) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | .array #[.link anonCid, .link metaCid] => acc.insert ⟨⟨anonCid⟩, ⟨metaCid⟩⟩
    | _ => none

def univAnonMapFromIpld (ar : Array Ipld) :
    Option (Std.RBMap (UnivCid .anon) (Univ .anon) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | .array #[.link cid, ipld] => do acc.insert ⟨cid⟩ (← univAnonFromIpld ipld)
    | _ => none

def univMetaMapFromIpld (ar : Array Ipld) :
    Option (Std.RBMap (UnivCid .meta) (Univ .meta) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | .array #[.link cid, ipld] => do acc.insert ⟨cid⟩ (← univMetaFromIpld ipld)
    | _ => none

def exprAnonMapFromIpld (ar : Array Ipld) :
    Option (Std.RBMap (ExprCid .anon) (Expr .anon) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | .array #[.link cid, ipld] => do acc.insert ⟨cid⟩ (← exprAnonFromIpld ipld)
    | _ => none

def exprMetaMapFromIpld (ar : Array Ipld) :
    Option (Std.RBMap (ExprCid .meta) (Expr .meta) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | .array #[.link cid, ipld] => do acc.insert ⟨cid⟩ (← exprMetaFromIpld ipld)
    | _ => none

def constAnonMapFromIpld (ar : Array Ipld) :
    Option (Std.RBMap (ConstCid .anon) (Const .anon) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | .array #[.link cid, ipld] => do acc.insert ⟨cid⟩ (← constAnonFromIpld ipld)
    | _ => none

def constMetaMapFromIpld (ar : Array Ipld) :
    Option (Std.RBMap (ConstCid .meta) (Const .meta) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | .array #[.link cid, ipld] => do acc.insert ⟨cid⟩ (← constMetaFromIpld ipld)
    | _ => none

def storeFromIpld : Ipld → Option IR.Store
  | .array #[
    .array constsIpld,
    .array univAnonIpld,
    .array exprAnonIpld,
    .array constAnonIpld,
    .array univMetaIpld,
    .array exprMetaIpld,
    .array constMetaIpld] =>
    return ⟨
      ← constsTreeFromIpld   constsIpld,
      ← univAnonMapFromIpld  univAnonIpld,
      ← exprAnonMapFromIpld  exprAnonIpld,
      ← constAnonMapFromIpld constAnonIpld,
      ← univMetaMapFromIpld  univMetaIpld,
      ← exprMetaMapFromIpld  exprMetaIpld,
      ← constMetaMapFromIpld constMetaIpld⟩
  | _ => none

end Yatima.Ipld
