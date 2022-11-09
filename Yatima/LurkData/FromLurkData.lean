import Yatima.Datatypes.Store
import Yatima.LurkData.Move

namespace Yatima.LurkData

open Lurk.Syntax AST

def toNat : AST → Option Nat
  | .num n => return n
  | _ => none

def toBool : AST → Option Bool
  | .t => return true
  | .nil => return false
  | _ => none

def toNat? : AST → Option (Option Nat)
  | ~[.num n] => return some n
  | .nil => return none
  | _ => none

def toList (es : AST) : Option $ List AST :=
  match es.telescopeCons with
  | (es, .nil) => es.data
  | _ => none

def toName (parts : AST) : Option Name := do
  (← toList parts).foldlM (init := .anonymous) fun acc i =>
    match i with
    | .num n => pure $ acc.mkNum n
    | .str s => pure $ acc.mkStr s
    | _ => none

def toListName (es : AST) : Option (List Name) := do
  (← toList es).mapM toName

def toBinderInfo : AST → Option BinderInfo
  | .num 0 => return .default
  | .num 1 => return .implicit
  | .num 2 => return .strictImplicit
  | .num 3 => return .instImplicit
  | _ => none

def toQuotKind : AST → Option QuotKind
  | .num 0 => return .type
  | .num 1 => return .ctor
  | .num 2 => return .lift
  | .num 3 => return .ind
  | _ => none

def toDefinitionSafety : AST → Option DefinitionSafety
  | .num 0 => return .safe
  | .num 1 => return .unsafe
  | .num 2 => return .partial
  | _ => none

def toLiteral : AST → Option Literal
  | .str s => return .strVal s
  | .num n => return .natVal n
  | _ => none

open IR

def toNatₐ : (k : Kind) → AST → Option (Natₐ k)
  | .anon, .cons (.num 0) x => return .injₗ (← toNat x)
  | .meta, .cons (.num 1) .nil => return .injᵣ ()
  | _, _ => none

def toBoolₐ : (k : Kind) → AST → Option (Boolₐ k)
  | .anon, .cons (.num 0) b => return .injₗ (← toBool b)
  | .meta, .cons (.num 1) .nil => return .injᵣ ()
  | _, _ => none

def toSplitNatₐNameₘ : (k : Kind) → AST → Option (NatₐNameₘ k)
  | .anon, .cons (.num 0) x => return .injₗ (← toNat x)
  | .meta, .cons (.num 1) x => return .injᵣ (← toName x)
  | _, _ => none

def toNat?ₘ : (k : Kind) → AST → Option (Nat?ₘ k)
  | .anon, .cons (.num 0) .nil => return .injₗ ()
  | .meta, .cons (.num 1) x => return .injᵣ (← toNat? x)
  | _, _ => none

def toNameₘ : (k : Kind) → AST → Option (Nameₘ k)
  | .anon, .cons (.num 0) .nil => return .injₗ ()
  | .meta, .cons (.num 1) x => return .injᵣ (← toName x)
  | _, _ => none

def toNatₐListNameₘ : (k : Kind) → AST → Option (NatₐListNameₘ k)
  | .anon, .cons (.num 0) x => return .injₗ (← toNat x)
  | .meta, .cons (.num 1) x => return .injᵣ (← toListName x)
  | _, _ => none

def toBinderInfoₐ : (k : Kind) → AST → Option (BinderInfoₐ k)
  | .anon, .cons (.num 0) x => return .injₗ (← toBinderInfo x)
  | .meta, .cons (.num 1) .nil => return .injᵣ ()
  | _, _ => none

def toSplitLiteralUnit : (k : Kind) → AST → Option (Split Literal Unit k)
  | .anon, .cons (.num 0) x => return .injₗ (← toLiteral x)
  | .meta, .cons (.num 1) .nil => return .injᵣ ()
  | _, _ => none

def toSplitQuotKind : (k : Kind) → AST → Option (Split QuotKind Unit k)
  | .anon, .cons (.num 0) x => return .injₗ (← toQuotKind x)
  | .meta, .cons (.num 1) .nil => return .injᵣ ()
  | _, _ => none

def toSplitDefinitionSafetyUnit :
    (k : Kind) → AST → Option (Split DefinitionSafety Unit k)
  | .anon, .cons (.num 0) x => return .injₗ (← toDefinitionSafety x)
  | .meta, .cons (.num 1) .nil => return .injᵣ ()
  | _, _ => none

def toUnivCid : AST → Option (UnivCid k)
  | ~[.comm, .num c] => return ⟨.ofNat c⟩
  | _ => none

def toExprCid : AST → Option (ExprCid k)
  | ~[.comm, .num c] => return ⟨.ofNat c⟩
  | _ => none

def toConstCid : AST → Option (ConstCid k)
  | ~[.comm, .num c] => return ⟨.ofNat c⟩
  | _ => none

def toListUnivCid (es : AST) : Option (List (UnivCid k)) := do
  (← toList es).mapM toUnivCid

def toDefinition : AST → Option (Definition k)
  | ~[n, l, ty, v, s] =>
    return ⟨← toNameₘ k n, ← toNatₐListNameₘ k l, ← toExprCid ty, ← toExprCid v,
      ← toSplitDefinitionSafetyUnit k s⟩
  | _ => none

def toListDefinition (es : AST) : Option (List (Definition k)) := do
  (← toList es).mapM toDefinition

def toMutDef :
    (k : Kind) → AST → Option (Split (Definition k) (List (Definition k)) k)
  | .anon, .cons (.num 0) x => return .injₗ (← toDefinition x)
  | .meta, .cons (.num 1) x => return .injᵣ (← toListDefinition x)
  | _, _ => none

def toMutDefBlock :
    (k : Kind) → AST → Option (List (Split (Definition k) (List (Definition k)) k))
  | .anon, es => do (← toList es).mapM $ toMutDef .anon
  | .meta, es => do (← toList es).mapM $ toMutDef .meta

def toConstructor : AST → Option (Constructor k)
  | ~[n, ty, l, i, p, f, r, s] =>
    return ⟨← toNameₘ k n, ← toNatₐListNameₘ k ty,
      ← toExprCid l, ← toNatₐ k i, ← toNatₐ k p,
      ← toNatₐ k f, ← toExprCid r, ← toBoolₐ k s⟩
  | _ => none

def toListConstructor (es : AST) : Option (List (Constructor k)) := do
  (← toList es).mapM toConstructor

def toRecursorRule : AST → Option (RecursorRule k)
  | ~[c, f, r] => return ⟨← toConstCid c, ← toNatₐ k f, ← toExprCid r⟩
  | _ => none

def toListRecursorRule (es : AST) : Option (List (RecursorRule k)) := do
  (← toList es).mapM toRecursorRule

def toSplitUnitListRecursorRule :
    (r : RecType) → AST → Option (Split Unit (List (RecursorRule k)) r)
  | .intr, .cons (.num 0) .nil => return .injₗ ()
  | .extr, .cons (.num 1) x => return .injᵣ (← toListRecursorRule x)
  | _, _ => none

def toRecType : AST → Option RecType
  | .t   => return .intr
  | .nil => return .extr
  | _ => none

def toSigmaRecursor : AST → Option (Sigma (Recursor · k))
  | ~[b, n, l, ty, p, i, m, m', rs, k'] => do
    let recType ← toRecType b
    return ⟨recType,
      ⟨← toNameₘ k n, ← toNatₐListNameₘ k l, ← toExprCid ty,
        ← toNatₐ k p, ← toNatₐ k i,
        ← toNatₐ k m, ← toNatₐ k m',
        ← toSplitUnitListRecursorRule recType rs,
        ← toBoolₐ k k'⟩⟩
  | _ => none

def toListSigmaRecursor (es : AST) : Option (List (Sigma (Recursor · k))) := do
  (← toList es).mapM toSigmaRecursor

def mutIndFromIpld : AST → Option (Inductive k)
  | ~[n, l, ty, p, i, cs, rs, r, s, r'] =>
    return ⟨← toNameₘ k n, ← toNatₐListNameₘ k l,
      ← toExprCid ty, ← toNatₐ k p, ← toNatₐ k i,
      ← toListConstructor cs,
      ← toListSigmaRecursor rs,
      ← toBoolₐ k r, ← toBoolₐ k s, ← toBoolₐ k r'⟩
  | _ => none

def toMutIndBlock (es : AST) : Option (List (Inductive k)) := do
  (← toList es).mapM mutIndFromIpld

def toUnivAnon : AST → Option (Univ .anon)
  | ~[.u64 $ UNIV .anon, .num 0] =>
    return .zero
  | ~[.u64 $ UNIV .anon, .num 1, p] =>
    return .succ (← toUnivCid p)
  | ~[.u64 $ UNIV .anon, .num 2, a, b] =>
    return .max (← toUnivCid a) (← toUnivCid b)
  | ~[.u64 $ UNIV .anon, .num 3, a, b] =>
    return .imax (← toUnivCid a) (← toUnivCid b)
  | ~[.u64 $ UNIV .anon, .num 4, n] =>
    return .var (← toSplitNatₐNameₘ .anon n)
  | _ => none

def toUnivMeta : AST → Option (Univ .meta)
  | ~[.u64 $ UNIV .meta, .num 0] =>
    return .zero
  | ~[.u64 $ UNIV .meta, .num 1, p] =>
    return .succ (← toUnivCid p)
  | ~[.u64 $ UNIV .meta, .num 2, a, b] =>
    return .max (← toUnivCid a) (← toUnivCid b)
  | ~[.u64 $ UNIV .meta, .num 3, a, b] =>
    return .imax (← toUnivCid a) (← toUnivCid b)
  | ~[.u64 $ UNIV .meta, .num 4, n] =>
    return .var (← toSplitNatₐNameₘ .meta n)
  | _ => none

def toExprAnon : AST → Option (Expr .anon)
  | ~[.u64 $ EXPR .anon, .num 0, n, i, ls] =>
    return .var (← toSplitNatₐNameₘ .anon n) (← toNat?ₘ .anon i)
      (← toListUnivCid ls)
  | ~[.u64 $ EXPR .anon, .num 1, u] =>
    return .sort (← toUnivCid u)
  | ~[.u64 $ EXPR .anon, .num 2, n, c, ls] =>
    return .const (← toNameₘ .anon n) (← toConstCid c)
      (← toListUnivCid ls)
  | ~[.u64 $ EXPR .anon, .num 3, f, a] =>
    return .app (← toExprCid f) (← toExprCid a)
  | ~[.u64 $ EXPR .anon, .num 4, n, i, d, b] =>
    return .lam (← toNameₘ .anon n) (← toBinderInfoₐ .anon i)
      (← toExprCid d) (← toExprCid b)
  | ~[.u64 $ EXPR .anon, .num 5, n, i, d, b] =>
    return .pi (← toNameₘ .anon n) (← toBinderInfoₐ .anon i)
      (← toExprCid d) (← toExprCid b)
  | ~[.u64 $ EXPR .anon, .num 6, n, ty, v, b] =>
    return .letE (← toNameₘ .anon n) (← toExprCid ty)
      (← toExprCid v) (← toExprCid b)
  | ~[.u64 $ EXPR .anon, .num 7, l] =>
    return .lit (← toSplitLiteralUnit .anon l)
  | ~[.u64 $ EXPR .anon, .num 8, n, e] =>
    return .proj (← toNatₐ .anon n) (← toExprCid e)
  | _ => none

def toExprMeta : AST → Option (Expr .meta)
  | ~[.u64 $ EXPR .meta, .num 0, n, i, ls] =>
    return .var (← toSplitNatₐNameₘ .meta n) (← toNat?ₘ .meta i)
      (← toListUnivCid ls)
  | ~[.u64 $ EXPR .meta, .num 1, u] =>
    return .sort (← toUnivCid u)
  | ~[.u64 $ EXPR .meta, .num 2, n, c, ls] =>
    return .const (← toNameₘ .meta n) (← toConstCid c)
      (← toListUnivCid ls)
  | ~[.u64 $ EXPR .meta, .num 3, f, a] =>
    return .app (← toExprCid f) (← toExprCid a)
  | ~[.u64 $ EXPR .meta, .num 4, n, i, d, b] =>
    return .lam (← toNameₘ .meta n) (← toBinderInfoₐ .meta i)
      (← toExprCid d) (← toExprCid b)
  | ~[.u64 $ EXPR .meta, .num 5, n, i, d, b] =>
    return .pi (← toNameₘ .meta n) (← toBinderInfoₐ .meta i)
      (← toExprCid d) (← toExprCid b)
  | ~[.u64 $ EXPR .meta, .num 6, n, ty, v, b] =>
    return .letE (← toNameₘ .meta n) (← toExprCid ty)
      (← toExprCid v) (← toExprCid b)
  | ~[.u64 $ EXPR .meta, .num 7, l] =>
    return .lit (← toSplitLiteralUnit .meta l)
  | ~[.u64 $ EXPR .meta, .num 8, n, e] =>
    return .proj (← toNatₐ .meta n) (← toExprCid e)
  | _ => none

def toConstAnon : AST → Option (Const .anon)
  | ~[.u64 $ CONST .anon, .num 0, n, l, ty, s] =>
    return .axiom ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toBoolₐ .anon s⟩
  | ~[.u64 $ CONST .anon, .num 1, n, l, ty, v] =>
    return .theorem ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toExprCid v⟩
  | ~[.u64 $ CONST .anon, .num 2, n, l, ty, v, s] =>
    return .opaque ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toExprCid v, ← toBoolₐ .anon s⟩
  | ~[.u64 $ CONST .anon, .num 3, n, l, ty, k] =>
    return .quotient ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toSplitQuotKind .anon k⟩
  | ~[.u64 $ CONST .anon, .num 5, n, l, ty, b, i] =>
    return .inductiveProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .anon i⟩
  | ~[.u64 $ CONST .anon, .num 6, n, l, ty, b, i, j] =>
    return .constructorProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .anon i, ← toNatₐ .anon j⟩
  | ~[.u64 $ CONST .anon, .num 7, n, l, ty, b, i, j] =>
    return .recursorProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .anon i, ← toNatₐ .anon j⟩
  | ~[.u64 $ CONST .anon, .num 8, n, l, ty, b, i] =>
    return .definitionProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l,
      ← toExprCid ty, ← toConstCid b, ← toNat i⟩
  | ~[.u64 $ CONST .anon, .num 9, b] =>
    return .mutDefBlock (← toMutDefBlock .anon b)
  | ~[.u64 $ CONST .anon, .num 10, b] =>
    return .mutIndBlock (← toMutIndBlock b)
  | _ => none

def toConstMeta : AST → Option (Const .meta)
  | ~[.u64 $ CONST .meta, .num 0, n, l, ty, s] =>
    return .axiom ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toBoolₐ .meta s⟩
  | ~[.u64 $ CONST .meta, .num 1, n, l, ty, v] =>
    return .theorem ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toExprCid v⟩
  | ~[.u64 $ CONST .meta, .num 2, n, l, ty, v, s] =>
    return .opaque ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toExprCid v, ← toBoolₐ .meta s⟩
  | ~[.u64 $ CONST .meta, .num 3, n, l, ty, k] =>
    return .quotient ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toSplitQuotKind .meta k⟩
  | ~[.u64 $ CONST .meta, .num 5, n, l, ty, b, i] =>
    return .inductiveProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .meta i⟩
  | ~[.u64 $ CONST .meta, .num 6, n, l, ty, b, i, j] =>
    return .constructorProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .meta i, ← toNatₐ .meta j⟩
  | ~[.u64 $ CONST .meta, .num 7, n, l, ty, b, i, j] =>
    return .recursorProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toConstCid b, ← toNatₐ .meta i, ← toNatₐ .meta j⟩
  | ~[.u64 $ CONST .meta, .num 8, n, l, ty, b, i] =>
    return .definitionProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l,
      ← toExprCid ty, ← toConstCid b, ← toNat i⟩
  | ~[.u64 $ CONST .meta, .num 9, b] =>
    return .mutDefBlock (← toMutDefBlock .meta b)
  | ~[.u64 $ CONST .meta, .num 10, b] =>
    return .mutIndBlock (← toMutIndBlock b)
  | _ => none

def toConstsTree (ar : List AST) : Option (Std.RBSet BothConstCid compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[~[.comm, .num anonCid], ~[.comm, .num metaCid]] =>
      acc.insert ⟨⟨.ofNat anonCid⟩, ⟨.ofNat metaCid⟩⟩
    | _ => none

def toUnivAnonMap (ar : List AST) :
    Option (Std.RBMap (UnivCid .anon) (Univ .anon) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[~[.comm, .num cid], e] => do acc.insert ⟨.ofNat cid⟩ (← toUnivAnon e)
    | _ => none

def toUnivMetaMap (ar : List AST) :
    Option (Std.RBMap (UnivCid .meta) (Univ .meta) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[~[.comm, .num cid], e] => do acc.insert ⟨.ofNat cid⟩ (← toUnivMeta e)
    | _ => none

def toExprAnonMap (ar : List AST) :
    Option (Std.RBMap (ExprCid .anon) (Expr .anon) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[~[.comm, .num cid], e] => do acc.insert ⟨.ofNat cid⟩ (← toExprAnon e)
    | _ => none

def toExprMetaMap (ar : List AST) :
    Option (Std.RBMap (ExprCid .meta) (Expr .meta) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[~[.comm, .num cid], e] => do acc.insert ⟨.ofNat cid⟩ (← toExprMeta e)
    | _ => none

def toConstAnonMap (ar : List AST) :
    Option (Std.RBMap (ConstCid .anon) (Const .anon) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[~[.comm, .num cid], e] => do acc.insert ⟨.ofNat cid⟩ (← toConstAnon e)
    | _ => none

def toConstMetaMap (ar : List AST) :
    Option (Std.RBMap (ConstCid .meta) (Const .meta) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[~[.comm, .num cid], e] => do acc.insert ⟨.ofNat cid⟩ (← toConstMeta e)
    | _ => none

def storeFromIpld : AST → Option IR.Store
  | ~[.u64 STORE,
      consts,
      univAnon, exprAnon, constAnon,
      univMeta, exprMeta, constMeta] =>
    return ⟨
      ← toConstsTree   (← toList consts),
      ← toUnivAnonMap  (← toList univAnon),
      ← toExprAnonMap  (← toList exprAnon),
      ← toConstAnonMap (← toList constAnon),
      ← toUnivMetaMap  (← toList univMeta),
      ← toExprMetaMap  (← toList exprMeta),
      ← toConstMetaMap (← toList constMeta)⟩
  | _ => none

end Yatima.LurkData
