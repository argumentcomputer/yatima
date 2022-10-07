import Yatima.Datatypes.Store
import Yatima.LurkData.Move

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

def toList (es : Lurk.Expr) : Option $ List Lurk.Expr :=
  let rec aux (acc : List Lurk.Expr) : Lurk.Expr → Option (List Lurk.Expr)
    | .cons e e'@(.cons ..) => aux (e :: acc) e'
    | .cons e (.lit .nil) => e :: acc
    | _ => none
  aux [] es |>.map List.reverse

def toListName (es : Lurk.Expr) : Option (List Name) := do
  (← toList es).mapM toName

-- instance : OfNat (Fin Lurk.N) 0 := ⟨0, by simp⟩
-- instance : OfNat (Fin Lurk.N) 1 := ⟨1, by simp⟩
-- instance : OfNat (Fin Lurk.N) 2 := ⟨2, by simp⟩
-- instance : OfNat (Fin Lurk.N) 3 := ⟨3, by simp⟩
-- instance : OfNat (Fin Lurk.N) 4 := ⟨4, by simp⟩

def toBinderInfo : Lurk.Expr → Option BinderInfo
  | .nat 0 => return .default
  | .nat 1 => return .implicit
  | .nat 2 => return .strictImplicit
  | .nat 3 => return .instImplicit
  | .nat 4 => return .auxDecl
  | _ => none

def toQuotKind : Lurk.Expr → Option QuotKind
  | .nat 0 => return .type
  | .nat 1 => return .ctor
  | .nat 2 => return .lift
  | .nat 3 => return .ind
  | _ => none

def toDefinitionSafety : Lurk.Expr → Option DefinitionSafety
  | .nat 0 => return .safe
  | .nat 1 => return .unsafe
  | .nat 2 => return .partial
  | _ => none

def toLiteral : Lurk.Expr → Option Literal
  | .lit $ .str s => return .strVal s
  | .lit $ .num n => return .natVal n.val
  | _ => none

open IR

def toNatₐ : (k : Kind) → Lurk.Expr → Option (Natₐ k)
  | .anon, .cons (.nat 0) x => return .injₗ (← toNat x)
  | .meta, .cons (.nat 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def toBoolₐ : (k : Kind) → Lurk.Expr → Option (Boolₐ k)
  | .anon, .cons (.nat 0) b => return .injₗ (← toBool b)
  | .meta, .cons (.nat 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def toSplitNatₐNameₘ : (k : Kind) → Lurk.Expr → Option (NatₐNameₘ k)
  | .anon, .cons (.nat 0) x => return .injₗ (← toNat x)
  | .meta, .cons (.nat 1) x => return .injᵣ (← toName x)
  | _, _ => none

def toNat?ₘ : (k : Kind) → Lurk.Expr → Option (Nat?ₘ k)
  | .anon, .cons (.nat 0) (.lit .nil) => return .injₗ ()
  | .meta, .cons (.nat 1) x => return .injᵣ (← toNat? x)
  | _, _ => none

def toNameₘ : (k : Kind) → Lurk.Expr → Option (Nameₘ k)
  | .anon, .cons (.nat 0) (.lit .nil) => return .injₗ ()
  | .meta, .cons (.nat 1) x => return .injᵣ (← toName x)
  | _, _ => none

def toNatₐListNameₘ : (k : Kind) → Lurk.Expr → Option (NatₐListNameₘ k)
  | .anon, .cons (.nat 0) x => return .injₗ (← toNat x)
  | .meta, .cons (.nat 1) x => return .injᵣ (← toListName x)
  | _, _ => none

def toBinderInfoₐ : (k : Kind) → Lurk.Expr → Option (BinderInfoₐ k)
  | .anon, .cons (.nat 0) x => return .injₗ (← toBinderInfo x)
  | .meta, .cons (.nat 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def toSplitLiteralUnit : (k : Kind) → Lurk.Expr → Option (Split Literal Unit k)
  | .anon, .cons (.nat 0) x => return .injₗ (← toLiteral x)
  | .meta, .cons (.nat 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def toSplitQuotKind : (k : Kind) → Lurk.Expr → Option (Split QuotKind Unit k)
  | .anon, .cons (.nat 0) x => return .injₗ (← toQuotKind x)
  | .meta, .cons (.nat 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def toSplitDefinitionSafetyUnit :
    (k : Kind) → Lurk.Expr → Option (Split DefinitionSafety Unit k)
  | .anon, .cons (.nat 0) x => return .injₗ (← toDefinitionSafety x)
  | .meta, .cons (.nat 1) (.lit .nil) => return .injᵣ ()
  | _, _ => none

def toUnivCid : Lurk.Expr → Option (UnivCid k)
  | .comm (.lit $ .num c) => return ⟨c⟩
  | _ => none

def toExprCid : Lurk.Expr → Option (ExprCid k)
  | .comm (.lit $ .num c) => return ⟨c⟩
  | _ => none

def toConstCid : Lurk.Expr → Option (ConstCid k)
  | .comm (.lit $ .num c) => return ⟨c⟩
  | _ => none

def toListUnivCid (es : Lurk.Expr) : Option (List (UnivCid k)) := do
  (← toList es).mapM toUnivCid

def toDefinition : Lurk.Expr → Option (Definition k)
  | .mkList [n, l, ty, v, s] =>
    return ⟨← toNameₘ k n, ← toNatₐListNameₘ k l, ← toExprCid ty, ← toExprCid v,
      ← toSplitDefinitionSafetyUnit k s⟩
  | _ => none

def toListDefinition (es : Lurk.Expr) : Option (List (Definition k)) := do
  (← toList es).mapM toDefinition

def toMutDef :
    (k : Kind) → Lurk.Expr → Option (Split (Definition k) (List (Definition k)) k)
  | .anon, .cons (.nat 0) x => return .injₗ (← toDefinition x)
  | .meta, .cons (.nat 1) x => return .injᵣ (← toListDefinition x)
  | _, _ => none

def toMutDefBlock :
    (k : Kind) → Lurk.Expr → Option (List (Split (Definition k) (List (Definition k)) k))
  | .anon, es => do (← toList es).mapM $ toMutDef .anon
  | .meta, es => do (← toList es).mapM $ toMutDef .meta

def toConstructor : Lurk.Expr → Option (Constructor k)
  | .mkList [n, ty, l, i, p, f, r, s] =>
    return ⟨← toNameₘ k n, ← toNatₐListNameₘ k ty,
      ← toExprCid l, ← toNatₐ k i, ← toNatₐ k p,
      ← toNatₐ k f, ← toExprCid r, ← toBoolₐ k s⟩
  | _ => none

def toListConstructor (es : Lurk.Expr) : Option (List (Constructor k)) := do
  (← toList es).mapM toConstructor

def toRecursorRule : Lurk.Expr → Option (RecursorRule k)
  | .mkList [c, f, r] => return ⟨← toConstCid c, ← toNatₐ k f, ← toExprCid r⟩
  | _ => none

def toListRecursorRule (es : Lurk.Expr) : Option (List (RecursorRule k)) := do
  (← toList es).mapM toRecursorRule

def toSplitUnitListRecursorRule :
    (r : RecType) → Lurk.Expr → Option (Split Unit (List (RecursorRule k)) r)
  | .intr, .cons (.nat 0) (.lit .nil) => return .injₗ ()
  | .extr, .cons (.nat 1) x => return .injᵣ (← toListRecursorRule x)
  | _, _ => none

def toRecType : Lurk.Expr → Option RecType
  | .lit .t   => return .intr
  | .lit .nil => return .extr
  | _ => none

def toSigmaRecursor : Lurk.Expr → Option (Sigma (Recursor · k))
  | .mkList [b, n, l, ty, p, i, m, m', rs, k'] => do
    let recType ← toRecType b
    return ⟨recType,
      ⟨← toNameₘ k n, ← toNatₐListNameₘ k l, ← toExprCid ty,
        ← toNatₐ k p, ← toNatₐ k i,
        ← toNatₐ k m, ← toNatₐ k m',
        ← toSplitUnitListRecursorRule recType rs,
        ← toBoolₐ k k'⟩⟩
  | _ => none

def toListSigmaRecursor (es : Lurk.Expr) : Option (List (Sigma (Recursor · k))) := do
  (← toList es).mapM toSigmaRecursor

def mutIndFromIpld : Lurk.Expr → Option (Inductive k)
  | .mkList [n, l, ty, p, i, cs, rs, r, s, r'] =>
    return ⟨← toNameₘ k n, ← toNatₐListNameₘ k l,
      ← toExprCid ty, ← toNatₐ k p, ← toNatₐ k i,
      ← toListConstructor cs,
      ← toListSigmaRecursor rs,
      ← toBoolₐ k r, ← toBoolₐ k s, ← toBoolₐ k r'⟩
  | _ => none

def toMutIndBlock (es : Lurk.Expr) : Option (List (Inductive k)) := do
  (← toList es).mapM mutIndFromIpld

def univAnonFromIpld : Lurk.Expr → Option (Univ .anon)
  | .mkList [.u64 $ UNIV .anon, .nat 0] =>
    return .zero
  | .mkList [.u64 $ UNIV .anon, .nat 1, p] =>
    return .succ (← toUnivCid p)
  | .mkList [.u64 $ UNIV .anon, .nat 2, a, b] =>
    return .max (← toUnivCid a) (← toUnivCid b)
  | .mkList [.u64 $ UNIV .anon, .nat 3, a, b] =>
    return .imax (← toUnivCid a) (← toUnivCid b)
  | .mkList [.u64 $ UNIV .anon, .nat 4, n] =>
    return .var (← toSplitNatₐNameₘ .anon n)
  | _ => none

def univMetaFromIpld : Lurk.Expr → Option (Univ .meta)
  | .mkList [.u64 $ UNIV .meta, .nat 0] =>
    return .zero
  | .mkList [.u64 $ UNIV .meta, .nat 1, p] =>
    return .succ (← toUnivCid p)
  | .mkList [.u64 $ UNIV .meta, .nat 2, a, b] =>
    return .max (← toUnivCid a) (← toUnivCid b)
  | .mkList [.u64 $ UNIV .meta, .nat 3, a, b] =>
    return .imax (← toUnivCid a) (← toUnivCid b)
  | .mkList [.u64 $ UNIV .meta, .nat 4, n] =>
    return .var (← toSplitNatₐNameₘ .meta n)
  | _ => none

def exprAnonFromIpld : Lurk.Expr → Option (Expr .anon)
  | .mkList [.u64 $ EXPR .anon, .nat 0, n, i, ls] =>
    return .var (← toSplitNatₐNameₘ .anon n) (← toNat?ₘ .anon i)
      (← toListUnivCid ls)
  | .mkList [.u64 $ EXPR .anon, .nat 1, u] =>
    return .sort (← toUnivCid u)
  | .mkList [.u64 $ EXPR .anon, .nat 2, n, c, ls] =>
    return .const (← toNameₘ .anon n) (← toConstCid c)
      (← toListUnivCid ls)
  | .mkList [.u64 $ EXPR .anon, .nat 3, f, a] =>
    return .app (← toExprCid f) (← toExprCid a)
  | .mkList [.u64 $ EXPR .anon, .nat 4, n, i, d, b] =>
    return .lam (← toNameₘ .anon n) (← toBinderInfoₐ .anon i)
      (← toExprCid d) (← toExprCid b)
  | .mkList [.u64 $ EXPR .anon, .nat 5, n, i, d, b] =>
    return .pi (← toNameₘ .anon n) (← toBinderInfoₐ .anon i)
      (← toExprCid d) (← toExprCid b)
  | .mkList [.u64 $ EXPR .anon, .nat 6, n, ty, v, b] =>
    return .letE (← toNameₘ .anon n) (← toExprCid ty)
      (← toExprCid v) (← toExprCid b)
  | .mkList [.u64 $ EXPR .anon, .nat 7, l] =>
    return .lit (← toSplitLiteralUnit .anon l)
  | .mkList [.u64 $ EXPR .anon, .nat 8, n, e] =>
    return .proj (← toNatₐ .anon n) (← toExprCid e)
  | _ => none

def exprMetaFromIpld : Lurk.Expr → Option (Expr .meta)
  | .mkList [.u64 $ EXPR .meta, .nat 0, n, i, ls] =>
    return .var (← toSplitNatₐNameₘ .meta n) (← toNat?ₘ .meta i)
      (← toListUnivCid ls)
  | .mkList [.u64 $ EXPR .meta, .nat 1, u] =>
    return .sort (← toUnivCid u)
  | .mkList [.u64 $ EXPR .meta, .nat 2, n, c, ls] =>
    return .const (← toNameₘ .meta n) (← toConstCid c)
      (← toListUnivCid ls)
  | .mkList [.u64 $ EXPR .meta, .nat 3, f, a] =>
    return .app (← toExprCid f) (← toExprCid a)
  | .mkList [.u64 $ EXPR .meta, .nat 4, n, i, d, b] =>
    return .lam (← toNameₘ .meta n) (← toBinderInfoₐ .meta i)
      (← toExprCid d) (← toExprCid b)
  | .mkList [.u64 $ EXPR .meta, .nat 5, n, i, d, b] =>
    return .pi (← toNameₘ .meta n) (← toBinderInfoₐ .meta i)
      (← toExprCid d) (← toExprCid b)
  | .mkList [.u64 $ EXPR .meta, .nat 6, n, ty, v, b] =>
    return .letE (← toNameₘ .meta n) (← toExprCid ty)
      (← toExprCid v) (← toExprCid b)
  | .mkList [.u64 $ EXPR .meta, .nat 7, l] =>
    return .lit (← toSplitLiteralUnit .meta l)
  | .mkList [.u64 $ EXPR .meta, .nat 8, n, e] =>
    return .proj (← toNatₐ .meta n) (← toExprCid e)
  | _ => none

def constAnonFromIpld : Lurk.Expr → Option (Const .anon)
  | .mkList [.u64 $ CONST .anon, .nat 0, n, l, ty, s] =>
    return .axiom ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toBoolₐ .anon s⟩
  | .mkList [.u64 $ CONST .anon, .nat 1, n, l, ty, v] =>
    return .theorem ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toExprCid v⟩
  | .mkList [.u64 $ CONST .anon, .nat 2, n, l, ty, v, s] =>
    return .opaque ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toExprCid v, ← toBoolₐ .anon s⟩
  | .mkList [.u64 $ CONST .anon, .nat 3, n, l, ty, k] =>
    return .quotient ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toSplitQuotKind .anon k⟩
  | .mkList [.u64 $ CONST .anon, .nat 5, n, l, ty, b, i] =>
    return .inductiveProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .anon i⟩
  | .mkList [.u64 $ CONST .anon, .nat 6, n, l, ty, b, i, j] =>
    return .constructorProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .anon i, ← toNatₐ .anon j⟩
  | .mkList [.u64 $ CONST .anon, .nat 7, n, l, ty, b, i, j] =>
    return .recursorProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .anon i, ← toNatₐ .anon j⟩
  | .mkList [.u64 $ CONST .anon, .nat 8, n, l, ty, b, i] =>
    return .definitionProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toConstCid b, ← toNat i⟩
  | .mkList [.u64 $ CONST .anon, .nat 9, b] =>
    return .mutDefBlock (← toMutDefBlock .anon b)
  | .mkList [.u64 $ CONST .anon, .nat 10, b] =>
    return .mutIndBlock (← toMutIndBlock b)
  | _ => none

def constMetaFromIpld : Lurk.Expr → Option (Const .meta)
  | .mkList [.u64 $ CONST .meta, .nat 0, n, l, ty, s] =>
    return .axiom ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toBoolₐ .meta s⟩
  | .mkList [.u64 $ CONST .meta, .nat 1, n, l, ty, v] =>
    return .theorem ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toExprCid v⟩
  | .mkList [.u64 $ CONST .meta, .nat 2, n, l, ty, v, s] =>
    return .opaque ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toExprCid v, ← toBoolₐ .meta s⟩
  | .mkList [.u64 $ CONST .meta, .nat 3, n, l, ty, k] =>
    return .quotient ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toSplitQuotKind .meta k⟩
  | .mkList [.u64 $ CONST .meta, .nat 5, n, l, ty, b, i] =>
    return .inductiveProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .meta i⟩
  | .mkList [.u64 $ CONST .meta, .nat 6, n, l, ty, b, i, j] =>
    return .constructorProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .meta i, ← toNatₐ .meta j⟩
  | .mkList [.u64 $ CONST .meta, .nat 7, n, l, ty, b, i, j] =>
    return .recursorProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .meta i, ← toNatₐ .meta j⟩
  | .mkList [.u64 $ CONST .meta, .nat 8, n, l, ty, b, i] =>
    return .definitionProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toConstCid b, ← toNat i⟩
  | .mkList [.u64 $ CONST .meta, .nat 9, b] =>
    return .mutDefBlock (← toMutDefBlock .meta b)
  | .mkList [.u64 $ CONST .meta, .nat 10, b] =>
    return .mutIndBlock (← toMutIndBlock b)
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

def storeFromIpld : Lurk.Expr → Option IR.Store
  | .mkList [
    .u64 STORE,
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
