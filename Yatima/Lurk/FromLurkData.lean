import Yatima.Datatypes.Store
import Lurk.Hashing.Datatypes

namespace Yatima.Lurk

open Lurk.Syntax AST

def toNat : AST → Option Nat
  | .num n => return n
  | _ => none

def toBool : AST → Option Bool
  | .sym "T" => return true
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

def toTag : Nat → Option Lurk.Tag
  | 0 => some .nil
  | 1 => some .cons
  | 2 => some .sym
  | 3 => some .fun
  | 4 => some .num
  | 5 => some .thunk
  | 6 => some .str
  | 7 => some .char
  | 8 => some .comm
  | _ => none

def toUnivScalar : AST → Option (UnivScalar k)
  | ~[.num t, .num v] => return ⟨← toTag t, .ofNat v⟩
  | _ => none

def toExprScalar : AST → Option (ExprScalar k)
  | ~[.num t, .num v] => return ⟨← toTag t, .ofNat v⟩
  | _ => none

def toConstScalar : AST → Option (ConstScalar k)
  | ~[.num t, .num v] => return ⟨← toTag t, .ofNat v⟩
  | _ => none

def toListUnivScalar (es : AST) : Option (List (UnivScalar k)) := do
  (← toList es).mapM toUnivScalar

def toDefinition : AST → Option (Definition k)
  | ~[n, l, ty, v, s] =>
    return ⟨← toNameₘ k n, ← toNatₐListNameₘ k l, ← toExprScalar ty, ← toExprScalar v,
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
      ← toExprScalar l, ← toNatₐ k i, ← toNatₐ k p,
      ← toNatₐ k f, ← toExprScalar r, ← toBoolₐ k s⟩
  | _ => none

def toListConstructor (es : AST) : Option (List (Constructor k)) := do
  (← toList es).mapM toConstructor

def toRecursorRule : AST → Option (RecursorRule k)
  | ~[c, f, r] => return ⟨← toConstScalar c, ← toNatₐ k f, ← toExprScalar r⟩
  | _ => none

def toListRecursorRule (es : AST) : Option (List (RecursorRule k)) := do
  (← toList es).mapM toRecursorRule

def toSplitUnitListRecursorRule :
    (r : RecType) → AST → Option (Split Unit (List (RecursorRule k)) r)
  | .intr, .cons (.num 0) .nil => return .injₗ ()
  | .extr, .cons (.num 1) x => return .injᵣ (← toListRecursorRule x)
  | _, _ => none

def toRecType : AST → Option RecType
  | .sym "T" => return .intr
  | .nil => return .extr
  | _ => none

def toSigmaRecursor : AST → Option (Sigma (Recursor · k))
  | ~[b, n, l, ty, p, i, m, m', rs, k'] => do
    let recType ← toRecType b
    return ⟨recType,
      ⟨← toNameₘ k n, ← toNatₐListNameₘ k l, ← toExprScalar ty,
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
      ← toExprScalar ty, ← toNatₐ k p, ← toNatₐ k i,
      ← toListConstructor cs,
      ← toListSigmaRecursor rs,
      ← toBoolₐ k r, ← toBoolₐ k s, ← toBoolₐ k r'⟩
  | _ => none

def toMutIndBlock (es : AST) : Option (List (Inductive k)) := do
  (← toList es).mapM mutIndFromIpld

def toUnivAnon : AST → Option (Univ .anon)
  | ~[.num 0]       => return .zero
  | ~[.num 1, p]    => return .succ (← toUnivScalar p)
  | ~[.num 2, a, b] => return .max (← toUnivScalar a) (← toUnivScalar b)
  | ~[.num 3, a, b] => return .imax (← toUnivScalar a) (← toUnivScalar b)
  | ~[.num 4, n]    => return .var (← toSplitNatₐNameₘ .anon n)
  | _ => none

def toUnivMeta : AST → Option (Univ .meta)
  | ~[.num 0]       => return .zero
  | ~[.num 1, p]    => return .succ (← toUnivScalar p)
  | ~[.num 2, a, b] => return .max (← toUnivScalar a) (← toUnivScalar b)
  | ~[.num 3, a, b] => return .imax (← toUnivScalar a) (← toUnivScalar b)
  | ~[.num 4, n]    => return .var (← toSplitNatₐNameₘ .meta n)
  | _ => none

def toExprAnon : AST → Option (Expr .anon)
  | ~[.num 0, n, i, ls]    =>
    return .var (← toSplitNatₐNameₘ .anon n) (← toNat?ₘ .anon i) (← toListUnivScalar ls)
  | ~[.num 1, u]           =>
    return .sort (← toUnivScalar u)
  | ~[.num 2, n, c, ls]    =>
    return .const (← toNameₘ .anon n) (← toConstScalar c) (← toListUnivScalar ls)
  | ~[.num 3, f, a]        =>
    return .app (← toExprScalar f) (← toExprScalar a)
  | ~[.num 4, n, i, d, b]  =>
    return .lam (← toNameₘ .anon n) (← toBinderInfoₐ .anon i) (← toExprScalar d) (← toExprScalar b)
  | ~[.num 5, n, i, d, b]  =>
    return .pi (← toNameₘ .anon n) (← toBinderInfoₐ .anon i) (← toExprScalar d) (← toExprScalar b)
  | ~[.num 6, n, ty, v, b] =>
    return .letE (← toNameₘ .anon n) (← toExprScalar ty) (← toExprScalar v) (← toExprScalar b)
  | ~[.num 7, l]           =>
    return .lit (← toSplitLiteralUnit .anon l)
  | ~[.num 8, n, e]        =>
    return .proj (← toNatₐ .anon n) (← toExprScalar e)
  | _ => none

def toExprMeta : AST → Option (Expr .meta)
  | ~[.num 0, n, i, ls]    =>
    return .var (← toSplitNatₐNameₘ .meta n) (← toNat?ₘ .meta i) (← toListUnivScalar ls)
  | ~[.num 1, u]           =>
    return .sort (← toUnivScalar u)
  | ~[.num 2, n, c, ls]    =>
    return .const (← toNameₘ .meta n) (← toConstScalar c) (← toListUnivScalar ls)
  | ~[.num 3, f, a]        =>
    return .app (← toExprScalar f) (← toExprScalar a)
  | ~[.num 4, n, i, d, b]  =>
    return .lam (← toNameₘ .meta n) (← toBinderInfoₐ .meta i) (← toExprScalar d) (← toExprScalar b)
  | ~[.num 5, n, i, d, b]  =>
    return .pi (← toNameₘ .meta n) (← toBinderInfoₐ .meta i) (← toExprScalar d) (← toExprScalar b)
  | ~[.num 6, n, ty, v, b] =>
    return .letE (← toNameₘ .meta n) (← toExprScalar ty) (← toExprScalar v) (← toExprScalar b)
  | ~[.num 7, l]           =>
    return .lit (← toSplitLiteralUnit .meta l)
  | ~[.num 8, n, e]        =>
    return .proj (← toNatₐ .meta n) (← toExprScalar e)
  | _ => none

def toConstAnon : AST → Option (Const .anon)
  | ~[.num 0, n, l, ty, s]       =>
    return .axiom ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l, ← toExprScalar ty, ← toBoolₐ .anon s⟩
  | ~[.num 1, n, l, ty, v]       =>
    return .theorem ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l, ← toExprScalar ty, ← toExprScalar v⟩
  | ~[.num 2, n, l, ty, v, s]    =>
    return .opaque ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l, ← toExprScalar ty, ← toExprScalar v, ← toBoolₐ .anon s⟩
  | ~[.num 3, n, l, ty, k]       =>
    return .quotient ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l, ← toExprScalar ty, ← toSplitQuotKind .anon k⟩
  | ~[.num 5, n, l, ty, b, i]    =>
    return .inductiveProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l, ← toExprScalar ty, ← toConstScalar b, ← toNatₐ .anon i⟩
  | ~[.num 6, n, l, ty, b, i, j] =>
    return .constructorProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l, ← toExprScalar ty, ← toConstScalar b, ← toNatₐ .anon i, ← toNatₐ .anon j⟩
  | ~[.num 7, n, l, ty, b, i, j] =>
    return .recursorProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l, ← toExprScalar ty, ← toConstScalar b, ← toNatₐ .anon i, ← toNatₐ .anon j⟩
  | ~[.num 8, n, l, ty, b, i]    =>
    return .definitionProj ⟨← toNameₘ .anon n, ← toNatₐListNameₘ .anon l, ← toExprScalar ty, ← toConstScalar b, ← toNat i⟩
  | ~[.num 9, b]                 =>
    return .mutDefBlock (← toMutDefBlock .anon b)
  | ~[.num 10, b]                =>
    return .mutIndBlock (← toMutIndBlock b)
  | _ => none

def toConstMeta : AST → Option (Const .meta)
  | ~[.num 0, n, l, ty, s]       =>
    return .axiom ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l, ← toExprScalar ty, ← toBoolₐ .meta s⟩
  | ~[.num 1, n, l, ty, v]       =>
    return .theorem ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l, ← toExprScalar ty, ← toExprScalar v⟩
  | ~[.num 2, n, l, ty, v, s]    =>
    return .opaque ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l, ← toExprScalar ty, ← toExprScalar v, ← toBoolₐ .meta s⟩
  | ~[.num 3, n, l, ty, k]       =>
    return .quotient ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l, ← toExprScalar ty, ← toSplitQuotKind .meta k⟩
  | ~[.num 5, n, l, ty, b, i]    =>
    return .inductiveProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l, ← toExprScalar ty, ← toConstScalar b, ← toNatₐ .meta i⟩
  | ~[.num 6, n, l, ty, b, i, j] =>
    return .constructorProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l, ← toExprScalar ty, ← toConstScalar b, ← toNatₐ .meta i, ← toNatₐ .meta j⟩
  | ~[.num 7, n, l, ty, b, i, j] =>
    return .recursorProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l, ← toExprScalar ty, ← toConstScalar b, ← toNatₐ .meta i, ← toNatₐ .meta j⟩
  | ~[.num 8, n, l, ty, b, i]    =>
    return .definitionProj ⟨← toNameₘ .meta n, ← toNatₐListNameₘ .meta l, ← toExprScalar ty, ← toConstScalar b, ← toNat i⟩
  | ~[.num 9, b]                 =>
    return .mutDefBlock (← toMutDefBlock .meta b)
  | ~[.num 10, b]                =>
    return .mutIndBlock (← toMutIndBlock b)
  | _ => none

def toConstsTree (ar : List AST) : Option (Std.RBSet BothConstScalar compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[anon, meta] => do acc.insert ⟨← toConstScalar anon, ← toConstScalar meta⟩
    | _ => none

def toUnivAnonMap (ar : List AST) :
    Option (Std.RBMap (UnivScalar .anon) (Univ .anon) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[ptr, e] => do acc.insert (← toUnivScalar ptr) (← toUnivAnon e)
    | _ => none

def toUnivMetaMap (ar : List AST) :
    Option (Std.RBMap (UnivScalar .meta) (Univ .meta) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[ptr, e] => do acc.insert (← toUnivScalar ptr) (← toUnivMeta e)
    | _ => none

def toExprAnonMap (ar : List AST) :
    Option (Std.RBMap (ExprScalar .anon) (Expr .anon) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[ptr, e] => do acc.insert (← toExprScalar ptr) (← toExprAnon e)
    | _ => none

def toExprMetaMap (ar : List AST) :
    Option (Std.RBMap (ExprScalar .meta) (Expr .meta) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[ptr, e] => do acc.insert (← toExprScalar ptr) (← toExprMeta e)
    | _ => none

def toConstAnonMap (ar : List AST) :
    Option (Std.RBMap (ConstScalar .anon) (Const .anon) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[ptr, e] => do acc.insert (← toConstScalar ptr) (← toConstAnon e)
    | _ => none

def toConstMetaMap (ar : List AST) :
    Option (Std.RBMap (ConstScalar .meta) (Const .meta) compare) :=
  ar.foldlM (init := default) fun acc pair =>
    match pair with
    | ~[ptr, e] => do acc.insert (← toConstScalar ptr) (← toConstMeta e)
    | _ => none

def toStore : AST → Option IR.Store
  | ~[consts,
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

end Yatima.Lurk
