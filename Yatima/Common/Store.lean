import Yatima.Datatypes.Const
import Std.Data.RBMap
import Yatima.Common.IO
import Yatima.Common.LightData

namespace Yatima

namespace IR

open Std (RBMap RBSet)

structure Visited where
  univs  : RBSet Hash compare
  exprs  : RBSet Hash compare
  consts : RBSet Hash compare
  deriving Inhabited

abbrev LoadM α := ReaderT Visited $ ExceptT String $ StateT α IO

def withVisitedUniv (hash : Hash) : LoadM τ α → LoadM τ α :=
  withReader fun visited => { visited with univs := visited.univs.insert hash }

def withVisitedExpr (hash : Hash) : LoadM τ α → LoadM τ α :=
  withReader fun visited => { visited with exprs := visited.exprs.insert hash }

def withVisitedConst (hash : Hash) : LoadM τ α → LoadM τ α :=
  withReader fun visited => {visited with consts := visited.consts.insert hash}

structure StoreAnon where
  univs  : RBMap Hash UnivAnon  compare
  exprs  : RBMap Hash ExprAnon  compare
  consts : RBMap Hash ConstAnon compare
  deriving Inhabited, BEq

namespace StoreAnon

partial def loadUniv (hash : Hash) : LoadM StoreAnon Unit := do
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

partial def loadConst (hash : Hash) : LoadM StoreAnon Unit := do
  if (← get).consts.contains hash then return
  if (← read).consts.contains hash then
    throw s!"Cycle detected for ConstAnon hash {hash}"
  withVisitedConst hash do
    let path := CONSTANONDIR / hash.data.toHex
    let some const ← loadData path
      | throw s!"{path} not found"
    modify fun store => {store with consts := store.consts.insert hash const}
    loadConstInternals const

partial def loadConstInternals : ConstAnon → LoadM StoreAnon Unit
  | .axiom ⟨_, x, _⟩
  | .quotient ⟨_, x, _⟩ => loadExpr x
  | .theorem ⟨_, x, y⟩
  | .opaque ⟨_, x, y, _⟩
  | .definition ⟨_, x, y, _⟩ => do loadExpr x; loadExpr y
  | .inductiveProj ⟨x, _⟩
  | .constructorProj ⟨x, _, _⟩
  | .recursorProj ⟨x, _, _⟩
  | .definitionProj ⟨x, _⟩ => loadConst x
  | .mutDefBlock ds => ds.forM fun d => do loadExpr d.type; loadExpr d.value
  | .mutIndBlock is => is.forM fun i => do
    loadExpr i.type
    i.ctors.forM (loadExpr ·.type)
    i.recrs.forM fun r => do loadExpr r.type; r.rules.forM (loadExpr ·.rhs)

partial def loadExpr (hash : Hash) : LoadM StoreAnon Unit := do
  if (← get).exprs.contains hash then return
  if (← read).exprs.contains hash then
    throw s!"Cycle detected for ExprAnon hash {hash}"
  withVisitedConst hash do
    let path := EXPRANONDIR / hash.data.toHex
    let some expr ← loadData path
      | throw s!"{path} not found"
    modify fun store => { store with exprs := store.exprs.insert hash expr }
    loadExprInternals expr

partial def loadExprInternals : ExprAnon → LoadM StoreAnon Unit
  | .var _ us => us.forM loadUniv
  | .sort u => loadUniv u
  | .const c us => do loadConst c; us.forM loadUniv
  | .app x y | .lam x y | .pi x y => do loadExpr x; loadExpr y
  | .letE x y z => do loadExpr x; loadExpr y; loadExpr z
  | .proj _ x => loadExpr x
  | .lit _ => pure ()

end

@[inline] def loadM (hashes : Array Hash) : LoadM StoreAnon Unit :=
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
  deriving Inhabited, BEq

namespace StoreMeta

partial def loadUniv (hash : Hash) : LoadM StoreMeta Unit := do
  if (← get).univs.contains hash then return
  if (← read).univs.contains hash then
    throw s!"Cycle detected for UnivAnon hash {hash}"
  withVisitedUniv hash do
    let path := UNIVMETADIR / hash.data.toHex
    let some univ ← loadData path
      | throw s!"{path} not found"
    modify fun store => { store with univs := store.univs.insert hash univ }
    match univ with
    | .succ x => loadUniv x
    | .max x y | .imax x y => do loadUniv x; loadUniv y
    | _ => pure ()

mutual

partial def loadConst (hash : Hash) : LoadM StoreMeta Unit := do
  if (← get).consts.contains hash then return
  if (← read).consts.contains hash then
    throw s!"Cycle detected for ConstAnon hash {hash}"
  withVisitedConst hash do
    let path := CONSTMETADIR / hash.data.toHex
    let some const ← loadData path
      | throw s!"{path} not found"
    modify fun store => {store with consts := store.consts.insert hash const}
    loadConstInternals const

partial def loadConstInternals : ConstMeta → LoadM StoreMeta Unit
  | .axiom ⟨_, _, x⟩
  | .quotient ⟨_, _, x⟩ => loadExpr x
  | .theorem ⟨_, _, x, y⟩
  | .opaque ⟨_, _, x, y⟩
  | .definition ⟨_, _, x, y⟩ => do loadExpr x; loadExpr y
  | .inductiveProj ⟨x, _⟩
  | .constructorProj ⟨x, _, _⟩
  | .recursorProj ⟨x, _, _⟩
  | .definitionProj ⟨x, _⟩ => loadConst x
  | .mutDefBlock dss => dss.forM fun ds =>
    ds.forM fun d => do loadExpr d.type; loadExpr d.value
  | .mutIndBlock is => is.forM fun i => do
    loadExpr i.type
    i.ctors.forM (loadExpr ·.type)
    i.recrs.forM fun r => do loadExpr r.type; r.rules.forM (loadExpr ·.rhs)

partial def loadExpr (hash : Hash) : LoadM StoreMeta Unit := do
  if (← get).exprs.contains hash then return
  if (← read).exprs.contains hash then
    throw s!"Cycle detected for ExprAnon hash {hash}"
  withVisitedConst hash do
    let path := EXPRMETADIR / hash.data.toHex
    let some expr ← loadData path
      | throw s!"{path} not found"
    modify fun store => { store with exprs := store.exprs.insert hash expr }
    loadExprInternals expr

partial def loadExprInternals : ExprMeta → LoadM StoreMeta Unit
  | .var _ _ us => us.forM loadUniv
  | .sort u => loadUniv u
  | .const c us => do loadConst c; us.forM loadUniv
  | .app x y | .lam _ _ x y | .pi _ _ x y => do loadExpr x; loadExpr y
  | .letE _ x y z => do loadExpr x; loadExpr y; loadExpr z
  | .proj x => loadExpr x
  | .lit => pure ()

end

@[inline] def loadM (hashes : Array Hash) : LoadM StoreMeta Unit :=
  hashes.forM loadConst

def load (hashes : Array Hash) : IO $ Except String StoreMeta := do
  match ← StateT.run (ReaderT.run (loadM hashes) default) default with
  | (.error e, _) => return .error e
  | (.ok _, store) => return .ok store

end StoreMeta

end IR

open Lurk (F) in
abbrev TC.Store := Std.RBMap F Const compare

end Yatima
