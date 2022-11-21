import Yatima.Datatypes.Store
import Lurk.Syntax.AST

namespace Yatima.Transpiler

open IR
open Lurk.Syntax (AST)

structure TranspileEnv where
  store : Store
  /-- Used to speed up lookup by name -/
  map : Std.RBMap Name (Both Const) compare
  overrides : Std.RBMap Name AST compare

structure TranspileState where
  appendedBindings : Array (Name × AST)
  /-- Contains the names of constants that have already been processed -/
  visited  : Lean.NameSet
  /-- These will help us replace hygienic/clashing names -/
  ngen     : Lean.NameGenerator
  replaced : Lean.NameMap Name
  deriving Inhabited

abbrev TranspileM := ReaderT TranspileEnv $
  ExceptT String $ StateM TranspileState

instance : Lean.MonadNameGenerator TranspileM where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen := ngen }

/-- Set `name` as a visited node -/
def visit (name : Name) : TranspileM Unit :=
  modify fun s => { s with visited := s.visited.insert name }

/-- Create a fresh variable to replace `name` and update `replaced` -/
def replace (name : Name) : TranspileM Name := do
  let mut name' ← Lean.mkFreshId
  let map := (← read).map
  while map.contains name' do -- making sure we don't hit an existing name
    name' ← Lean.mkFreshId
  modifyGet fun stt => (name', { stt with replaced := stt.replaced.insert name name' })

@[inline] def isVisited (n : Name) : TranspileM Bool :=
  return (← get).visited.contains n

def derefExpr (cid : Both ExprCid) : TranspileM $ Both Expr := do
  let store := (← read).store
  match (store.exprAnon.find? cid.anon, store.exprMeta.find? cid.meta) with
  | (some anon, some meta) => pure ⟨anon, meta⟩
  | _ => throw ""

def derefDefBlock (cid : Both ConstCid) : TranspileM $ List (Both Definition) := do
  let store := (← read).store
  match (store.constAnon.find? cid.anon, store.constMeta.find? cid.meta) with
  | (some $ .mutDefBlock anon, some $ .mutDefBlock meta) =>
    let mut ret := []
    for (anon, metas) in anon.zip meta do
      let anon := anon.projₗ
      let metas := metas.projᵣ
      let zip := (List.replicate metas.length anon).zip metas |>.map
        fun (x, y) => ⟨x, y⟩
      ret := zip :: ret
    return ret.join
  | _ => throw ""

def derefIndBlock (cid : Both ConstCid) : TranspileM $ List (Both Inductive) := do
  let store := (← read).store
  match (store.constAnon.find? cid.anon, store.constMeta.find? cid.meta) with
  | (some $ .mutIndBlock anons, some $ .mutIndBlock metas) =>
    return anons.zip metas |>.map fun (x, y) => ⟨x, y⟩
  | _ => throw ""
