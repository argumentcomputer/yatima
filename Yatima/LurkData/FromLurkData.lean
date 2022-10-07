import Yatima.Datatypes.Store

/-! 
We follow the convention `LurkData.to<object>`
-/
namespace Yatima.LurkData

def toNat : Lurk.Expr → Option Nat
  | .lit $ .num n => return n.val
  | _ => none

def toBool : Lurk.Expr → Option Bool
  | .lit .t => return true
  | .lit .nil => return false
  | _ => none

def toNat? : Lurk.Expr → Option (Option Nat)
  | .lit $ .num n => return some n.val
  | .lit .nil => return none
  | _ => none

def toName : Lurk.Expr → Option Name
  | .sym name => return name
  | _ => none

def toListName (ns : Lurk.Expr) : Option (List Name) :=
  let rec aux (acc : List Name) : Lurk.Expr → Option (List Name)
    | .cons (.sym n) ns => aux (n :: acc) ns
    | .sym n => n :: acc
    | _ => none
  (aux [] ns).map List.reverse

instance : OfNat (Fin Lurk.N) 0 := ⟨0, by simp⟩
instance : OfNat (Fin Lurk.N) 1 := ⟨1, by simp⟩
instance : OfNat (Fin Lurk.N) 2 := ⟨2, by simp⟩
instance : OfNat (Fin Lurk.N) 3 := ⟨3, by simp⟩
instance : OfNat (Fin Lurk.N) 4 := ⟨4, by simp⟩

def toBinderInfo : Lurk.Expr → Option BinderInfo
  | .lit $ .num 0 => return .default
  | .lit $ .num 1 => return .implicit
  | .lit $ .num 2 => return .strictImplicit
  | .lit $ .num 3 => return .instImplicit
  | .lit $ .num 4 => return .auxDecl
  | _ => none

def toQuotKind : Lurk.Expr → Option QuotKind
  | .lit $ .num 0 => return .type
  | .lit $ .num 1 => return .ctor
  | .lit $ .num 2 => return .lift
  | .lit $ .num 3 => return .ind
  | _ => none

def toDefinitionSafety : Lurk.Expr → Option DefinitionSafety
  | .lit $ .num 0 => return .safe
  | .lit $ .num 1 => return .unsafe
  | .lit $ .num 2 => return .partial
  | _ => none

def toLiteral : Lurk.Expr → Option Literal
  | .lit $ .str s => return .strVal s
  | .lit $ .num n => return .natVal n.val
  | _ => none

open IR

def toNatₐ : (k : Kind) → Lurk.Expr → Option (Natₐ k)
  | .anon, .cons (.lit $ .num 0) x => return .injₗ (← toNat x)
  | .meta, .cons (.lit $ .num 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def toBoolₐ : (k : Kind) → Lurk.Expr → Option (Boolₐ k)
  | .anon, .cons (.lit $ .num 0) b => return .injₗ (← toBool b)
  | .meta, .cons (.lit $ .num 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def splitNatₐNameₘFromIpld : (k : Kind) → Lurk.Expr → Option (NatₐNameₘ k)
  | .anon, .cons (.lit $ .num 0) x => return .injₗ (← toNat x)
  | .meta, .cons (.lit $ .num 1) x => return .injᵣ (← toName x)
  | _, _ => none

def toNat?ₘ : (k : Kind) → Lurk.Expr → Option (Nat?ₘ k)
  | .anon, .cons (.lit $ .num 0) (.lit .nil) => return .injₗ ()
  | .meta, .cons (.lit $ .num 1) x => return .injᵣ (← toNat? x)
  | _, _ => none

def toNameₘ : (k : Kind) → Lurk.Expr → Option (Nameₘ k)
  | .anon, .cons (.lit $ .num 0) (.lit .nil) => return .injₗ ()
  | .meta, .cons (.lit $ .num 1) x => return .injᵣ (← toName x)
  | _, _ => none

def toNatₐListNameₘ : (k : Kind) → Lurk.Expr → Option (NatₐListNameₘ k)
  | .anon, .cons (.lit $ .num 0) x => return .injₗ (← toNat x)
  | .meta, .cons (.lit $ .num 1) x => return .injᵣ (← toListName x)
  | _, _ => none

def toBinderInfoₐ : (k : Kind) → Lurk.Expr → Option (BinderInfoₐ k)
  | .anon, .cons (.lit $ .num 0) x => return .injₗ (← toBinderInfo x)
  | .meta, .cons (.lit $ .num 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def toSplitLiteralUnit : (k : Kind) → Lurk.Expr → Option (Split Literal Unit k)
  | .anon, .cons (.lit $ .num 0) x => return .injₗ (← toLiteral x)
  | .meta, .cons (.lit $ .num 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def splitQuotKindFromIpld : (k : Kind) → Lurk.Expr → Option (Split QuotKind Unit k)
  | .anon, .cons (.lit $ .num 0) x => return .injₗ (← toQuotKind x)
  | .meta, .cons (.lit $ .num 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def splitDefinitionSafetyUnitFromIpld :
    (k : Kind) → Lurk.Expr → Option (Split DefinitionSafety Unit k)
  | .anon, .cons (.lit $ .num 0) x => return .injₗ (← toDefinitionSafety x)
  | .meta, .cons (.lit $ .num 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def univCidFromIpld : Lurk.Expr → Option (UnivCid k)
  | .comm c => return ⟨c⟩
  | _ => none

def exprCidFromIpld : Lurk.Expr → Option (ExprCid k)
  | .link c => return ⟨c⟩
  | _ => none

def constCidFromIpld : Lurk.Expr → Option (ConstCid k)
  | .link c => return ⟨c⟩
  | _ => none

def listUnivCidFromIpld : Ipld → Option (List (UnivCid k))
  | .array ar => ar.data.mapM univCidFromIpld
  | _ => none

def definitionFromIpld : Ipld → Option (Definition k)
  | .array #[n, l, t, v, s] =>
    return ⟨← splitNameₘFromIpld k n, ← splitNatₐListNameₘFromIpld k l,
      ← exprCidFromIpld t, ← exprCidFromIpld v,
      ← splitDefinitionSafetyUnitFromIpld k s⟩
  | _ => none

def listDefinitionFromIpld : Ipld → Option (List (Definition k))
  | .array ar => ar.data.mapM definitionFromIpld
  | _ => none

def mutDefFromIpld :
    (k : Kind) → Ipld → Option (Split (Definition k) (List (Definition k)) k)
  | .anon, .array #[.number 0, x] => return .injₗ (← definitionFromIpld x)
  | .meta, .array #[.number 1, x] => return .injᵣ (← listDefinitionFromIpld x)
  | _, _ => none

def mutDefBlockFromIpld :
    (k : Kind) → Ipld → Option (List (Split (Definition k) (List (Definition k)) k))
  | .anon, .array ar => ar.data.mapM $ mutDefFromIpld .anon
  | .meta, .array ar => ar.data.mapM $ mutDefFromIpld .meta
  | _, _ => none

def constructorFromIpld : Ipld → Option (Constructor k)
  | .array #[n, t, l, i, p, f, r, s] =>
    return ⟨← splitNameₘFromIpld k n, ← splitNatₐListNameₘFromIpld k t,
      ← exprCidFromIpld l, ← splitNatₐFromIpld k i, ← splitNatₐFromIpld k p,
      ← splitNatₐFromIpld k f, ← exprCidFromIpld r, ← splitBoolₐFromIpld k s⟩
  | _ => none

def listConstructorFromIpld : Ipld → Option (List (Constructor k))
  | .array ar => ar.data.mapM constructorFromIpld
  | _ => none

def recursorRuleFromIpld : Ipld → Option (RecursorRule k)
  | .array #[c, f, r] =>
    return ⟨← constCidFromIpld c, ← splitNatₐFromIpld k f, ← exprCidFromIpld r⟩
  | _ => none

def listRecursorRuleFromIpld : Ipld → Option (List (RecursorRule k))
  | .array ar => ar.data.mapM recursorRuleFromIpld
  | _ => none

def splitUnitListRecursorRuleFromIpld :
    (r : RecType) → Ipld → Option (Split Unit (List (RecursorRule k)) r)
  | .intr, .array #[.number 0, .null] => return .injₗ ()
  | .extr, .array #[.number 1, x] => return .injᵣ (← listRecursorRuleFromIpld x)
  | _, _ => none

def recTypeFromIpld : Ipld → Option RecType
  | .bool true  => return .intr
  | .bool false => return .extr
  | _ => none

def sigmaRecursorFromIpld : Ipld → Option (Sigma (Recursor · k))
  | .array #[b, n, l, t, p, i, m, m', rs, k'] => do
    let recType ← recTypeFromIpld b
    return ⟨recType,
      ⟨← splitNameₘFromIpld k n, ← splitNatₐListNameₘFromIpld k l, ← exprCidFromIpld t,
        ← splitNatₐFromIpld k p, ← splitNatₐFromIpld k i,
        ← splitNatₐFromIpld k m, ← splitNatₐFromIpld k m',
        ← splitUnitListRecursorRuleFromIpld recType rs,
        ← splitBoolₐFromIpld k k'⟩⟩
  | _ => none

def listSigmaRecursorFromIpld : Ipld → Option (List (Sigma (Recursor · k)))
  | .array ar => ar.data.mapM sigmaRecursorFromIpld
  | _ => none

def mutIndFromIpld : Ipld → Option (Inductive k)
  | .array #[n, l, t, p, i, cs, rs, r, s, r'] =>
    return ⟨← splitNameₘFromIpld k n, ← splitNatₐListNameₘFromIpld k l,
      ← exprCidFromIpld t, ← splitNatₐFromIpld k p, ← splitNatₐFromIpld k i,
      ← listConstructorFromIpld cs,
      ← listSigmaRecursorFromIpld rs,
      ← splitBoolₐFromIpld k r, ← splitBoolₐFromIpld k s, ← splitBoolₐFromIpld k r'⟩
  | _ => none

def mutIndBlockFromIpld : Ipld → Option (List (Inductive k))
  | .array ar => ar.data.mapM mutIndFromIpld
  | _ => none

def univAnonFromIpld : Ipld → Option (Univ .anon)
  | .array #[.number $ UNIV .anon, .number 0] =>
    return .zero
  | .array #[.number $ UNIV .anon, .number 1, p] =>
    return .succ (← univCidFromIpld p)
  | .array #[.number $ UNIV .anon, .number 2, a, b] =>
    return .max (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number $ UNIV .anon, .number 3, a, b] =>
    return .imax (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number $ UNIV .anon, .number 4, n] =>
    return .var (← splitNatₐNameₘFromIpld .anon n)
  | _ => none

def univMetaFromIpld : Ipld → Option (Univ .meta)
  | .array #[.number $ UNIV .meta, .number 0] => some .zero
  | .array #[.number $ UNIV .meta, .number 1, p] =>
    return .succ (← univCidFromIpld p)
  | .array #[.number $ UNIV .meta, .number 2, a, b] =>
    return .max (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number $ UNIV .meta, .number 3, a, b] =>
    return .imax (← univCidFromIpld a) (← univCidFromIpld b)
  | .array #[.number $ UNIV .meta, .number 4, n] =>
    return .var (← splitNatₐNameₘFromIpld .meta n)
  | _ => none

def exprAnonFromIpld : Ipld → Option (Expr .anon)
  | .array #[.number $ EXPR .anon, .number 0, n, i, ls] =>
    return .var (← splitNatₐNameₘFromIpld .anon n) (← splitNat?ₘFromIpld .anon i)
      (← listUnivCidFromIpld ls)
  | .array #[.number $ EXPR .anon, .number 1, u] =>
    return .sort (← univCidFromIpld u)
  | .array #[.number $ EXPR .anon, .number 2, n, c, ls] =>
    return .const (← splitNameₘFromIpld .anon n) (← constCidFromIpld c)
      (← listUnivCidFromIpld ls)
  | .array #[.number $ EXPR .anon, .number 3, f, a] =>
    return .app (← exprCidFromIpld f) (← exprCidFromIpld a)
  | .array #[.number $ EXPR .anon, .number 4, n, i, d, b] =>
    return .lam (← splitNameₘFromIpld .anon n) (← splitBinderInfoₐFromIpld .anon i)
      (← exprCidFromIpld d) (← exprCidFromIpld b)
  | .array #[.number $ EXPR .anon, .number 5, n, i, d, b] =>
    return .pi (← splitNameₘFromIpld .anon n) (← splitBinderInfoₐFromIpld .anon i)
      (← exprCidFromIpld d) (← exprCidFromIpld b)
  | .array #[.number $ EXPR .anon, .number 6, n, t, v, b] =>
    return .letE (← splitNameₘFromIpld .anon n) (← exprCidFromIpld t)
      (← exprCidFromIpld v) (← exprCidFromIpld b)
  | .array #[.number $ EXPR .anon, .number 7, l] =>
    return .lit (← splitLiteralUnitFromIpld .anon l)
  | .array #[.number $ EXPR .anon, .number 8, n, e] =>
    return .proj (← splitNatₐFromIpld .anon n) (← exprCidFromIpld e)
  | _ => none

def exprMetaFromIpld : Ipld → Option (Expr .meta)
  | .array #[.number $ EXPR .meta, .number 0, n, i, ls] =>
    return .var (← splitNatₐNameₘFromIpld .meta n) (← splitNat?ₘFromIpld .meta i)
      (← listUnivCidFromIpld ls)
  | .array #[.number $ EXPR .meta, .number 1, u] =>
    return .sort (← univCidFromIpld u)
  | .array #[.number $ EXPR .meta, .number 2, n, c, ls] =>
    return .const (← splitNameₘFromIpld .meta n) (← constCidFromIpld c)
      (← listUnivCidFromIpld ls)
  | .array #[.number $ EXPR .meta, .number 3, f, a] =>
    return .app (← exprCidFromIpld f) (← exprCidFromIpld a)
  | .array #[.number $ EXPR .meta, .number 4, n, i, d, b] =>
    return .lam (← splitNameₘFromIpld .meta n) (← splitBinderInfoₐFromIpld .meta i)
      (← exprCidFromIpld d) (← exprCidFromIpld b)
  | .array #[.number $ EXPR .meta, .number 5, n, i, d, b] =>
    return .pi (← splitNameₘFromIpld .meta n) (← splitBinderInfoₐFromIpld .meta i)
      (← exprCidFromIpld d) (← exprCidFromIpld b)
  | .array #[.number $ EXPR .meta, .number 6, n, t, v, b] =>
    return .letE (← splitNameₘFromIpld .meta n) (← exprCidFromIpld t)
      (← exprCidFromIpld v) (← exprCidFromIpld b)
  | .array #[.number $ EXPR .meta, .number 7, l] =>
    return .lit (← splitLiteralUnitFromIpld .meta l)
  | .array #[.number $ EXPR .meta, .number 8, n, e] =>
    return .proj (← splitNatₐFromIpld .meta n) (← exprCidFromIpld e)
  | _ => none

def constAnonFromIpld : Ipld → Option (Const .anon)
  | .array #[.number $ CONST .anon, .number 0, n, l, t, s] =>
    return .axiom ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← splitBoolₐFromIpld .anon s⟩
  | .array #[.number $ CONST .anon, .number 1, n, l, t, v] =>
    return .theorem ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← exprCidFromIpld v⟩
  | .array #[.number $ CONST .anon, .number 2, n, l, t, v, s] =>
    return .opaque ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← exprCidFromIpld v, ← splitBoolₐFromIpld .anon s⟩
  | .array #[.number $ CONST .anon, .number 3, n, l, t, k] =>
    return .quotient ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← splitQuotKindFromIpld .anon k⟩
  | .array #[.number $ CONST .anon, .number 5, n, l, t, b, i] =>
    return .inductiveProj ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .anon i⟩
  | .array #[.number $ CONST .anon, .number 6, n, l, t, b, i, j] =>
    return .constructorProj ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .anon i, ← splitNatₐFromIpld .anon j⟩
  | .array #[.number $ CONST .anon, .number 7, n, l, t, b, i, j] =>
    return .recursorProj ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .anon i, ← splitNatₐFromIpld .anon j⟩
  | .array #[.number $ CONST .anon, .number 8, n, l, t, b, i] =>
    return .definitionProj ⟨← splitNameₘFromIpld .anon n, ← splitNatₐListNameₘFromIpld .anon l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← natFromIpld i⟩
  | .array #[.number $ CONST .anon, .number 9, b] =>
    return .mutDefBlock (← mutDefBlockFromIpld .anon b)
  | .array #[.number $ CONST .anon, .number 10, b] =>
    return .mutIndBlock (← mutIndBlockFromIpld b)
  | _ => none

def constMetaFromIpld : Ipld → Option (Const .meta)
  | .array #[.number $ CONST .meta, .number 0, n, l, t, s] =>
    return .axiom ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← splitBoolₐFromIpld .meta s⟩
  | .array #[.number $ CONST .meta, .number 1, n, l, t, v] =>
    return .theorem ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← exprCidFromIpld v⟩
  | .array #[.number $ CONST .meta, .number 2, n, l, t, v, s] =>
    return .opaque ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← exprCidFromIpld v, ← splitBoolₐFromIpld .meta s⟩
  | .array #[.number $ CONST .meta, .number 3, n, l, t, k] =>
    return .quotient ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← splitQuotKindFromIpld .meta k⟩
  | .array #[.number $ CONST .meta, .number 5, n, l, t, b, i] =>
    return .inductiveProj ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .meta i⟩
  | .array #[.number $ CONST .meta, .number 6, n, l, t, b, i, j] =>
    return .constructorProj ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .meta i, ← splitNatₐFromIpld .meta j⟩
  | .array #[.number $ CONST .meta, .number 7, n, l, t, b, i, j] =>
    return .recursorProj ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← splitNatₐFromIpld .meta i, ← splitNatₐFromIpld .meta j⟩
  | .array #[.number $ CONST .meta, .number 8, n, l, t, b, i] =>
    return .definitionProj ⟨← splitNameₘFromIpld .meta n, ← splitNatₐListNameₘFromIpld .meta l,
      ← exprCidFromIpld t, ← constCidFromIpld b, ← natFromIpld i⟩
  | .array #[.number $ CONST .meta, .number 9, b] =>
    return .mutDefBlock (← mutDefBlockFromIpld .meta b)
  | .array #[.number $ CONST .meta, .number 10, b] =>
    return .mutIndBlock (← mutIndBlockFromIpld b)
  | _ => none

def constsTreeFromIpld (ar : Array Ipld) :
    Option (Std.RBTree (Both ConstCid) compare) :=
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
    .number STORE,
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

end Yatima.LurkData
