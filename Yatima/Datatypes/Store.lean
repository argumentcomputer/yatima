import Ipld.Ipld
import Yatima.Datatypes.Const
import Yatima.Typechecker.Datatypes

namespace Yatima

namespace IR

open Std (RBMap RBSet) in
/-- The end result of the compilation process -/
structure Store where
  consts : RBSet (Both ConstCid) compare

  univAnon  : RBMap (UnivCid  .anon) (Univ  .anon) compare
  exprAnon  : RBMap (ExprCid  .anon) (Expr  .anon) compare
  constAnon : RBMap (ConstCid .anon) (Const .anon) compare

  univMeta  : RBMap (UnivCid  .meta) (Univ  .meta) compare
  exprMeta  : RBMap (ExprCid  .meta) (Expr  .meta) compare
  constMeta : RBMap (ConstCid .meta) (Const .meta) compare
  deriving Inhabited

instance : BEq Store where
  beq x y := x.consts.toList == y.consts.toList
    && x.univAnon.toList  == y.univAnon.toList
    && x.exprAnon.toList  == y.exprAnon.toList
    && x.constAnon.toList == y.constAnon.toList
    && x.univMeta.toList  == y.univMeta.toList
    && x.univMeta.toList  == y.univMeta.toList
    && x.constMeta.toList == y.constMeta.toList

namespace Store

def union (s s' : Store) : Store := ⟨
  s'.consts.union s.consts,
  s'.univAnon.foldl  (init := s.univAnon)  fun acc cid x => acc.insert cid x,
  s'.exprAnon.foldl  (init := s.exprAnon)  fun acc cid x => acc.insert cid x,
  s'.constAnon.foldl (init := s.constAnon) fun acc cid x => acc.insert cid x,
  s'.univMeta.foldl  (init := s.univMeta)  fun acc cid x => acc.insert cid x,
  s'.exprMeta.foldl  (init := s.exprMeta)  fun acc cid x => acc.insert cid x,
  s'.constMeta.foldl (init := s.constMeta) fun acc cid x => acc.insert cid x
⟩

def getUniv? (store : Store) (cid : BothUnivCid) : Option (Both Univ) :=
  match (store.univAnon.find? cid.anon, store.univMeta.find? cid.meta) with
  | (some anon, some meta) => some ⟨anon, meta⟩
  | _ => none

def getExpr? (store : Store) (cid : BothExprCid) : Option (Both Expr) :=
  match (store.exprAnon.find? cid.anon, store.exprMeta.find? cid.meta) with
  | (some anon, some meta) => some ⟨anon, meta⟩
  | _ => none

def getConst? (store : Store) (cid : BothConstCid) : Option (Both Const) :=
  match (store.constAnon.find? cid.anon, store.constMeta.find? cid.meta) with
  | (some anon, some meta) => some ⟨anon, meta⟩
  | _ => none

def getAppFn (store : Store) : Both Expr → Option (Both Expr)
  | ⟨.app fAnon _, .app fMeta _⟩ => store.getExpr? ⟨fAnon, fMeta⟩
  | _ => none

partial def getAppArgs (store : Store) (acc : Array $ Both Expr) :
    Both Expr → Option (Array $ Both Expr)
  | ⟨.app _ aAnon, .app _ aMeta⟩ => do
    let a ← store.getExpr? ⟨aAnon, aMeta⟩
    store.getAppArgs (acc.push a) a
  | e => acc.push e

partial def telescopeLamPi (store : Store) (acc : Array Name) :
    Both Expr → Option ((Array Name) × Both Expr)
  | ⟨.lam _ _ _ bAnon, .lam n _ _ bMeta⟩
  | ⟨.pi  _ _ _ bAnon, .pi  n _ _ bMeta⟩ => do
    let b ← store.getExpr? ⟨bAnon, bMeta⟩
    store.telescopeLamPi (acc.push n.projᵣ) b
  | e => some (acc, e)

partial def telescopeLetE (store : Store) (acc : Array (Name × Both Expr)) :
    Both Expr → Option ((Array (Name × Both Expr)) × Both Expr)
  | ⟨.letE _ _ vAnon bAnon, .letE n _ vMeta bMeta⟩ => do
    let v ← store.getExpr? ⟨vAnon, vMeta⟩
    let b ← store.getExpr? ⟨bAnon, bMeta⟩
    store.telescopeLetE (acc.push (n.projᵣ, v)) b
  | e => some (acc, e)

end IR.Store

namespace TC

open Typechecker in
/-- Keeps track of the data used for typechecking -/
structure Store where
  consts       : Array Const
  primIdxs     : Std.RBMap PrimConst Nat compare
  idxsToPrims  : Std.RBMap Nat PrimConst compare
  deriving Inhabited

end TC

namespace Ipld

/-- Contains `IR.Store` data encoded in IPLD -/
structure Store where
  consts    : Array Ipld
  univAnon  : Array Ipld
  exprAnon  : Array Ipld
  constAnon : Array Ipld
  univMeta  : Array Ipld
  exprMeta  : Array Ipld
  constMeta : Array Ipld

end Ipld

end Yatima
