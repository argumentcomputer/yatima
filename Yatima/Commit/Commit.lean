import Yatima.Commit.CommitM
import Yatima.Commit.ToLDON
import Yatima.Datatypes.LightData
import Yatima.Common.IO

namespace Yatima.Commit

open IR TC Lurk

def loadUniv (hash : Hash) : CommitM $ Option Univ := do
  let path ← match (← get).univPaths.find? hash with
    | some path => pure path
    | none =>
      let path := UNIVDIR / hash.data.toHex
      modifyGet fun stt => (path, { stt with
        univPaths := stt.univPaths.insert hash path })
  if !(← path.pathExists) then return none
  let bytes ← IO.FS.readBinFile path
  sorry

def loadExpr (hash : Hash) : CommitM $ Option Expr := sorry
def loadConst (hash : Hash) : CommitM $ Option Const := sorry
def loadCommit (hash : Hash) : CommitM $ Option F := sorry

partial def mkTCUniv (hash : Hash) : CommitM Univ := do
  match (← get).univs.find? hash with
  | some u => pure u
  | none =>
    let u ← match ← loadUniv hash with
      | some u => pure u
      | none => match (← read).univs.find? hash with
        | none => throw sorry
        | some .zero => pure .zero
        | some $ .succ u => pure $ .succ (← mkTCUniv u)
        | some $ .max u v => pure $ .max (← mkTCUniv u) (← mkTCUniv v)
        | some $ .imax u v => pure $ .imax (← mkTCUniv u) (← mkTCUniv v)
        | some $ .var n => pure $ .var n
      persistData (Coe.coe u) $ (← get).univPaths.find! hash
    modifyGet fun stt => (u, { stt with univs := stt.univs.insert hash u })

mutual

partial def mkTCExpr (hash : Hash) : CommitM Expr := do
  match (← get).exprs.find? hash with
  | some e => pure e
  | none =>
    let e ← match ← loadExpr hash with
      | some e => pure e
      | none => match (← read).exprs.find? hash with
        | none => throw sorry
        | some $ .var i us => sorry
        | some $ .sort u => pure $ .sort (← mkTCUniv u)
        | some $ .const c us => pure $ .const (← commitConst c) (← us.mapM mkTCUniv)
        | some $ .app x y => pure $ .app (← mkTCExpr x) (← mkTCExpr y)
        | some $ .lam x y => pure $ .lam (← mkTCExpr x) (← mkTCExpr y)
        | some $ .pi  x y => pure $ .pi  (← mkTCExpr x) (← mkTCExpr y)
        | some $ .letE x y z => pure $ .letE (← mkTCExpr x) (← mkTCExpr y) (← mkTCExpr z)
        | some $ .lit l => pure $ .lit l
        | some $ .proj n e => pure $ .proj n (← mkTCExpr e)
      persistData (Coe.coe e) $ (← get).exprPaths.find! hash
    modifyGet fun stt => (e, { stt with exprs := stt.exprs.insert hash e })

partial def mkTCCtor : IR.ConstructorAnon → CommitM Constructor
  | ⟨lvls, typeHash, ids, params, fields, safe⟩ =>
    return ⟨lvls, ← mkTCExpr typeHash, ids, params, fields, safe⟩

partial def mkTCInd : IR.InductiveAnon → CommitM Inductive
  | ⟨lvls, type, params, indices, ctors, _, recr, safe, refl⟩ => do
    -- Structures can't be recursive nor have indices
    let (struct, unit) ← if recr || indices != 0 then pure (none, false) else
      match ctors with
      -- Structures can only have one constructor
      | [ctor] =>
        let f ← commitConst (ctor : LightData).hash -- can we avoid hashing?
        pure $ (some f, ctor.fields == 0)
      | _ => pure (none, false)
    return ⟨lvls, ← mkTCExpr type, params, indices, ← ctors.mapM mkTCCtor, recr,
      safe, refl, struct, unit⟩

partial def mkTCConst (hash : Hash) : CommitM Const := do
  match (← get).consts.find? hash with
  | some c => pure c
  | none =>
    let c ← match ← loadConst hash with
      | some c => pure c
      | none => match (← read).consts.find? hash with
        | none => throw sorry
        | some $ .axiom x => pure $ .axiom ⟨x.lvls, ← mkTCExpr x.type, x.safe⟩
        | some $ .theorem x => pure $ .theorem ⟨x.lvls, ← mkTCExpr x.type, ← mkTCExpr x.value⟩
        | some $ .opaque x => pure $ .opaque ⟨x.lvls, ← mkTCExpr x.type, ← mkTCExpr x.value, x.safe⟩
        | some $ .quotient x => pure $ .quotient ⟨x.lvls, ← mkTCExpr x.type, x.kind⟩
        | some $ .inductiveProj x =>
          match (← read).consts.find? x.block with
          | none => throw sorry
          | some $ .mutIndBlock inds =>
            let some ind := inds.get? x.idx | throw sorry
            pure $ .inductive $ ← mkTCInd ind
          | _ => throw sorry
        | some $ .constructorProj x =>
          match (← read).consts.find? x.block with
          | none => throw sorry
          | some $ .mutIndBlock inds =>
            let some ind := inds.get? x.idx | throw sorry
            let some ⟨lvls, type, idx, params, fields, safe⟩ := ind.ctors.get? x.idx | throw sorry
            pure $ .constructor ⟨lvls, ← mkTCExpr type, idx, params, fields, safe⟩
          | _ => throw sorry
        | some $ .recursorProj x =>
          match (← read).consts.find? x.block with
          | none => throw sorry
          | some $ .mutIndBlock inds =>
            let some ind := inds.get? x.idx | throw sorry
            let indF ← commitConst (ind : LightData).hash -- can we avoid hashing?
            let some ⟨lvls, type, params, indices, motives, minors, rules, isK, internal⟩ := ind.recrs.get? x.idx | throw sorry
            pure $ .recursor ⟨lvls, ← mkTCExpr type, params, indices, motives, minors, sorry, isK, internal, indF, sorry⟩
          | _ => throw sorry
        | some $ .definitionProj x =>
          match (← read).consts.find? x.block with
          | none => throw sorry
          | some $ .mutDefBlock defs =>
            let some ⟨lvls, type, value, safety⟩ := defs.get? x.idx | throw sorry
            pure $ .definition ⟨lvls, ← mkTCExpr type, ← mkTCExpr value, safety, sorry⟩
          | _ => throw sorry
        | some $ .mutDefBlock _ | some $ .mutIndBlock _ => throw sorry
      persistData (Coe.coe c) $ (← get).constPaths.find! hash
    modifyGet fun stt => (c, { stt with consts := stt.consts.insert hash c })

partial def commitConst (hash : Hash) : CommitM F := do
  match (← get).commits.find? hash with
  | some f => pure f
  | none => match ← loadCommit hash with
    | some f =>
      modifyGet fun stt => (f, {stt with commits := stt.commits.insert hash f})
    | none =>
      let const ← mkTCConst hash
      -- this is expensive
      let (f, encStt) := const.toLDON.commit (← get).ldonHashState
      persistData f $ (← get).commitPaths.find! hash
      modifyGet fun stt => (f, { stt with
        commits := stt.commits.insert hash f
        ldonHashState := encStt })

end

def commitM (hashes : Array Hash) : CommitM $ Array F := do
  let hashes ← hashes.mapM commitConst
  persistData (← get).ldonHashState LDONHASHCACHE
  return hashes

open Std (RBSet)

structure Visited where
  univs  : RBSet Hash compare
  exprs  : RBSet Hash compare
  consts : RBSet Hash compare
  deriving Inhabited

abbrev StoreM := ReaderT Visited $ ExceptT String $ StateT Store IO

def withVisitedUniv (hash : Hash) : StoreM α → StoreM α :=
  withReader fun visited => { visited with univs := visited.univs.insert hash }

def withVisitedExpr (hash : Hash) : StoreM α → StoreM α :=
  withReader fun visited => { visited with exprs := visited.exprs.insert hash }

def withVisitedConst (hash : Hash) : StoreM α → StoreM α :=
  withReader fun visited => {visited with consts := visited.consts.insert hash}

variable
  [hUniv  : Encodable UnivAnon  LightData String]
  [hExpr  : Encodable ExprAnon  LightData String]
  [hConst : Encodable ConstAnon LightData String]

partial def storeUniv (hash : Hash) : StoreM Unit := do
  if (← get).univs.contains hash then return
  if (← read).univs.contains hash then
    throw s!"Cycle detected for UnivAnon hash {hash}"
  withVisitedUniv hash do
    let path := UNIVANONDIR / hash.data.toHex
    if !(← path.pathExists) then throw s!"{path} not found"
    match LightData.ofByteArray (← IO.FS.readBinFile path) with
    | .error e => throw e
    | .ok data => match hUniv.decode data with
      | .error e => throw e
      | .ok univ =>
        modify fun store => { store with univs := store.univs.insert hash univ }
        match univ with
        | .succ x => storeUniv x
        | .max x y | .imax x y => do storeUniv x; storeUniv y
        | _ => pure ()

mutual

partial def storeConst (hash : Hash) : StoreM Unit := do
  if (← get).consts.contains hash then return
  if (← read).consts.contains hash then
    throw s!"Cycle detected for ConstAnon hash {hash}"
  withVisitedConst hash do
    let path := CONSTANONDIR / hash.data.toHex
    if !(← path.pathExists) then throw s!"{path} not found"
    match LightData.ofByteArray (← IO.FS.readBinFile path) with
    | .error e => throw e
    | .ok data => match hConst.decode data with
      | .error e => throw e
      | .ok const =>
        modify fun store => {store with consts := store.consts.insert hash const}
        storeConstInternals const

partial def storeConstInternals : ConstAnon → StoreM Unit
  | .axiom ⟨_, x, _⟩
  | .quotient ⟨_, x, _⟩ => storeExpr x
  | .theorem ⟨_, x, y⟩
  | .opaque ⟨_, x, y, _⟩ => do storeExpr x; storeExpr y
  | .inductiveProj ⟨_, x, y, _⟩
  | .constructorProj ⟨_, x, y, _, _⟩
  | .recursorProj ⟨_, x, y, _, _⟩
  | .definitionProj ⟨_, x, y, _⟩=> do storeExpr x; storeConst y
  | .mutDefBlock ds => ds.forM fun d => do storeExpr d.type; storeExpr d.value
  | .mutIndBlock is => is.forM fun i => do
    storeExpr i.type
    i.ctors.forM (storeExpr ·.type)
    i.recrs.forM fun r => do storeExpr r.type; r.rules.forM (storeExpr ·.rhs)

partial def storeExpr (hash : Hash) : StoreM Unit := do
  if (← get).exprs.contains hash then return
  if (← read).exprs.contains hash then
    throw s!"Cycle detected for ExprAnon hash {hash}"
  withVisitedConst hash do
    let path := EXPRANONDIR / hash.data.toHex
    if !(← path.pathExists) then throw s!"{path} not found"
    match LightData.ofByteArray (← IO.FS.readBinFile path) with
    | .error e => throw e
    | .ok data => match hExpr.decode data with
      | .error e => throw e
      | .ok expr =>
        modify fun store => { store with exprs := store.exprs.insert hash expr }
        storeExprInternals expr

partial def storeExprInternals : ExprAnon → StoreM Unit
  | .var _ us => us.forM storeUniv
  | .sort u => storeUniv u
  | .const c us => do storeConst c; us.forM storeUniv
  | .app x y | .lam x y | .pi x y => do storeExpr x; storeExpr y
  | .letE x y z => do storeExpr x; storeExpr y; storeExpr z
  | .proj _ x => storeExpr x
  | .lit _ => pure ()

end

@[inline] def mkStoreM (hashes : Array Hash) : StoreM Unit :=
  hashes.forM storeConst

def mkStore (hashes : Array Hash) : IO $ Except String Store := do
  match ← StateT.run (ReaderT.run (mkStoreM hashes) default) default with
  | (.error e, _) => return .error e
  | (.ok _, store) => return .ok store

def commit (hashes : Array Hash) : IO $ Except String (Array F) := do
  match ← mkStore hashes with
  | .error e => return .error e
  | .ok store =>
    match ← StateT.run (ReaderT.run (commitM hashes) store) default with
    | (.error e, _) => return .error e
    | (.ok hs, _) => return .ok hs

end Yatima.Commit
