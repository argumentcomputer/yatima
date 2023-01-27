import Yatima.Datatypes.Const
import Std.Data.RBMap
import Yatima.Common.IO
import Yatima.Common.LightData

namespace Yatima

namespace IR

open Std (RBMap)

structure StoreAnon where
  univs  : RBMap Hash UnivAnon  compare
  exprs  : RBMap Hash ExprAnon  compare
  consts : RBMap Hash ConstAnon compare
  deriving Inhabited, BEq

namespace StoreAnon

open Std (RBSet)

structure Visited where
  univs  : RBSet Hash compare
  exprs  : RBSet Hash compare
  consts : RBSet Hash compare
  deriving Inhabited

abbrev LoadM := ReaderT Visited $ ExceptT String $ StateT StoreAnon IO

def withVisitedUniv (hash : Hash) : LoadM α → LoadM α :=
  withReader fun visited => { visited with univs := visited.univs.insert hash }

def withVisitedExpr (hash : Hash) : LoadM α → LoadM α :=
  withReader fun visited => { visited with exprs := visited.exprs.insert hash }

def withVisitedConst (hash : Hash) : LoadM α → LoadM α :=
  withReader fun visited => {visited with consts := visited.consts.insert hash}

partial def loadUniv (hash : Hash) : LoadM Unit := do
  if (← get).univs.contains hash then return
  if (← read).univs.contains hash then
    throw s!"Cycle detected for UnivAnon hash {hash}"
  withVisitedUniv hash do
    let path := UNIVANONDIR / hash.data.toHex
    let some univ ← loadData path
      | throw s!"{path} not found"
    modify fun store => { store with univs := store.univs.insert hash univ }
    match univ with
    | .succ x => loadUniv x
    | .max x y | .imax x y => do loadUniv x; loadUniv y
    | _ => pure ()

mutual

partial def loadConst (hash : Hash) : LoadM Unit := do
  if (← get).consts.contains hash then return
  if (← read).consts.contains hash then
    throw s!"Cycle detected for ConstAnon hash {hash}"
  withVisitedConst hash do
    let path := CONSTANONDIR / hash.data.toHex
    let some const ← loadData path
      | throw s!"{path} not found"
    modify fun store => {store with consts := store.consts.insert hash const}
    loadConstInternals const

partial def loadConstInternals : ConstAnon → LoadM Unit
  | .axiom ⟨_, x, _⟩
  | .quotient ⟨_, x, _⟩ => loadExpr x
  | .theorem ⟨_, x, y⟩
  | .opaque ⟨_, x, y, _⟩ => do loadExpr x; loadExpr y
  | .inductiveProj ⟨_, x, y, _⟩
  | .constructorProj ⟨_, x, y, _, _⟩
  | .recursorProj ⟨_, x, y, _, _⟩
  | .definitionProj ⟨_, x, y, _⟩=> do loadExpr x; loadConst y
  | .mutDefBlock ds => ds.forM fun d => do loadExpr d.type; loadExpr d.value
  | .mutIndBlock is => is.forM fun i => do
    loadExpr i.type
    i.ctors.forM (loadExpr ·.type)
    i.recrs.forM fun r => do loadExpr r.type; r.rules.forM (loadExpr ·.rhs)

partial def loadExpr (hash : Hash) : LoadM Unit := do
  if (← get).exprs.contains hash then return
  if (← read).exprs.contains hash then
    throw s!"Cycle detected for ExprAnon hash {hash}"
  withVisitedConst hash do
    let path := EXPRANONDIR / hash.data.toHex
    let some expr ← loadData path
      | throw s!"{path} not found"
    modify fun store => { store with exprs := store.exprs.insert hash expr }
    loadExprInternals expr

partial def loadExprInternals : ExprAnon → LoadM Unit
  | .var _ us => us.forM loadUniv
  | .sort u => loadUniv u
  | .const c us => do loadConst c; us.forM loadUniv
  | .app x y | .lam x y | .pi x y => do loadExpr x; loadExpr y
  | .letE x y z => do loadExpr x; loadExpr y; loadExpr z
  | .proj _ x => loadExpr x
  | .lit _ => pure ()

end

@[inline] def loadM (hashes : Array Hash) : LoadM Unit :=
  hashes.forM loadConst

def load (hashes : Array Hash) : IO $ Except String StoreAnon := do
  match ← StateT.run (ReaderT.run (loadM hashes) default) default with
  | (.error e, _) => return .error e
  | (.ok _, store) => return .ok store

end StoreAnon

structure StoreMeta where
  univs  : RBMap Hash UnivMeta  compare
  exprs  : RBMap Hash ExprMeta  compare
  consts : RBMap Hash ConstMeta compare
  deriving Inhabited

end IR

namespace TC

open Lurk (F)

abbrev Store := Std.RBMap F Const compare

end TC

end Yatima
