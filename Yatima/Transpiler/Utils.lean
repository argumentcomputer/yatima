import Yatima.Datatypes.Store

def Lean.Name.isHygenic : Name → Bool
  | str p s => if s == "_hyg" then true else p.isHygenic
  | num p _ => p.isHygenic
  | _       => false

def List.takeLast (xs : List α) (n : Nat) : List α :=
  (xs.reverse.take n).reverse

namespace Yatima.IR.Store

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

partial def telescopeApp (store : Store) (acc : List $ Both Expr) :
    Both Expr → Option (List $ Both Expr)
  | ⟨.app fAnon aAnon, .app fMeta aMeta⟩ => do
    let f ← store.getExpr? ⟨fAnon, fMeta⟩
    let a ← store.getExpr? ⟨aAnon, aMeta⟩
    store.telescopeApp (a :: acc) f
  | e => some $ e :: acc

end Yatima.IR.Store
