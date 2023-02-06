import Yatima.Commit.CommitM
import Yatima.Commit.ToLDON
import Yatima.Common.LightData
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
  loadData path

def loadExpr (hash : Hash) : CommitM $ Option Expr := do
  let path ← match (← get).exprPaths.find? hash with
    | some path => pure path
    | none =>
      let path := EXPRDIR / hash.data.toHex
      modifyGet fun stt => (path, { stt with
        exprPaths := stt.exprPaths.insert hash path })
  loadData path

def loadConst (hash : Hash) : CommitM $ Option Const := do
  let path ← match (← get).constPaths.find? hash with
    | some path => pure path
    | none =>
      let path := CONSTDIR / hash.data.toHex
      modifyGet fun stt => (path, { stt with
        constPaths := stt.constPaths.insert hash path })
  loadData path

def loadCommit (hash : Hash) : CommitM $ Option F := do
  let path ← match (← get).commitPaths.find? hash with
    | some path => pure path
    | none =>
      let path := COMMITSDIR / hash.data.toHex
      modifyGet fun stt => (path, { stt with
        commitPaths := stt.commitPaths.insert hash path })
  loadData path

partial def mkUniv (hash : Hash) : CommitM Univ := do
  match (← get).univs.find? hash with
  | some u => pure u
  | none =>
    let u ← match ← loadUniv hash with
      | some u => pure u
      | none => match (← read).store.univs.find? hash with
        | none => throw s!"malformed store: encountered hash for `Univ` not found:\n  {hash}"
        | some .zero => pure .zero
        | some $ .succ u => pure $ .succ (← mkUniv u)
        | some $ .max u v => pure $ .max (← mkUniv u) (← mkUniv v)
        | some $ .imax u v => pure $ .imax (← mkUniv u) (← mkUniv v)
        | some $ .var n => pure $ .var n
      if (← read).persist then dumpData u $ (← get).univPaths.find! hash
    modifyGet fun stt => (u, { stt with univs := stt.univs.insert hash u })

mutual

partial def mkExpr (hash : Hash) : CommitM Expr := do
  match (← get).exprs.find? hash with
  | some e => pure e
  | none =>
    let e ← match ← loadExpr hash with
      | some e => pure e
      | none => match (← read).store.exprs.find? hash with
        | none => throw s!"malformed store: encountered hash for `Expr` not found:\n  {hash}"
        | some $ .var i us => pure $ .var i -- TODO: someone please check my work
        | some $ .sort u => pure $ .sort (← mkUniv u)
        | some $ .const c us => pure $ .const (← commitConst c) (← us.mapM mkUniv)
        | some $ .app x y => pure $ .app (← mkExpr x) (← mkExpr y)
        | some $ .lam x y => pure $ .lam (← mkExpr x) (← mkExpr y)
        | some $ .pi  x y => pure $ .pi  (← mkExpr x) (← mkExpr y)
        | some $ .letE x y z => pure $ .letE (← mkExpr x) (← mkExpr y) (← mkExpr z)
        | some $ .lit l => pure $ .lit l
        | some $ .proj n e => pure $ .proj n (← mkExpr e)
      if (← read).persist then dumpData e $ (← get).exprPaths.find! hash
    modifyGet fun stt => (e, { stt with exprs := stt.exprs.insert hash e })

partial def mkInd : IR.InductiveAnon → CommitM Inductive
  | ⟨lvls, type, params, indices, ctors, recrs, recr, safe, refl⟩ => do
    -- Structures can't be recursive nor have indices
    let (struct, unit) ← if recr || indices != 0 then pure (true, false) else
      match ctors with
      -- Structures can only have one constructor
      | [ctor] => pure (true, ctor.fields == 0)
      | _ => pure (false, false)
    return ⟨lvls, ← mkExpr type, params, indices, ← ctors.mapM mkCtor, ← recrs.mapM mkRecr, 
      recr, safe, refl, struct, unit⟩

partial def mkCtor : IR.ConstructorAnon → CommitM Constructor
  | ⟨lvls, typeHash, ids, params, fields, safe⟩ =>
    return ⟨lvls, ← mkExpr typeHash, ids, params, fields, safe⟩

partial def mkRecr : IR.RecursorAnon → CommitM Recursor
  | ⟨lvls, type, params, indices, motives, minors, rules, isK, internal⟩ =>
    return ⟨lvls, ← mkExpr type, params, indices, motives, minors, ← rules.mapM mkRecursorRule, isK, internal⟩

partial def mkRecursorRule : IR.RecursorRuleAnon → CommitM RecursorRule
  | ⟨fields, rhsHash⟩ =>
    return ⟨fields, ← mkExpr rhsHash⟩

partial def mkDefn : IR.DefinitionAnon → CommitM Definition
  | ⟨lvls, type, value, safety⟩ =>
    return ⟨lvls, ← mkExpr type, ← mkExpr value, safety⟩

partial def mkConst (hash : Hash) : CommitM Const := do
  match (← get).consts.find? hash with
  | some c => pure c
  | none =>
    let c ← match ← loadConst hash with
      | some c => pure c
      | none =>
        let some const := ((← read).store.consts.find? hash) 
          | throw s!"malformed store: encountered hash for `Const` not found:\n  {hash}"
        match const with
        | .axiom x => pure $ .axiom ⟨x.lvls, ← mkExpr x.type, x.safe⟩
        | .theorem x => pure $ .theorem ⟨x.lvls, ← mkExpr x.type, ← mkExpr x.value⟩
        | .opaque x => pure $ .opaque ⟨x.lvls, ← mkExpr x.type, ← mkExpr x.value, x.safe⟩
        | .definition x => pure $ .definition (← mkDefn x)
        | .quotient x => pure $ .quotient ⟨x.lvls, ← mkExpr x.type, x.kind⟩
        | .inductiveProj x =>
          let block ← commitConst x.block
          pure $ .inductiveProj ⟨block, x.idx⟩
        | .recursorProj x =>
          let block ← commitConst x.block
          pure $ .recursorProj ⟨block, x.idx, x.ridx⟩
        | .constructorProj x =>
          let block ← commitConst x.block
          pure $ .constructorProj ⟨block, x.idx, x.cidx⟩
        | .definitionProj x =>
          let block ← commitConst x.block
          pure $ .definitionProj ⟨block, x.idx⟩
        | .mutDefBlock x => pure $ .mutDefBlock (← x.mapM mkDefn)
        | .mutIndBlock x => pure $ .mutIndBlock (← x.mapM mkInd)
      if (← read).persist then dumpData c $ (← get).constPaths.find! hash
    modifyGet fun stt => (c, { stt with consts := stt.consts.insert hash c })

partial def commitConst (hash : Hash) : CommitM F := do
  match (← get).commits.find? hash with
  | some f => pure f
  | none => match ← loadCommit hash with
    | some f =>
      modifyGet fun stt => (f, {stt with commits := stt.commits.insert hash f})
    | none =>
      let const ← mkConst hash
      if (← read).quick then
        let f := .ofNat $ (Hashable.hash const).toNat
        modifyGet fun stt => (f, {stt with commits := stt.commits.insert hash f})
      else
        -- committing is expensive
        let (f, encStt) := const.toLDON.commit (← get).ldonHashState
        dumpData f $ (← get).commitPaths.find! hash
        modifyGet fun stt => (f, { stt with
          commits := stt.commits.insert hash f
          ldonHashState := encStt })

end

def commitM (hashes : Array Hash) : CommitM $ Array F := do
  let hashes ← hashes.mapM commitConst
  if (← read).persist then dumpData (← get).ldonHashState LDONHASHCACHE
  return hashes

/-- Quick commitments never persist data -/
def commit (hashes : Array Hash) (store : StoreAnon) (quick persist : Bool) :
    IO $ Except String (CommitState × Array F) := do
  let persist := if quick then false else persist
  if persist then mkCMDirs
  match ← StateT.run (ReaderT.run (commitM hashes)
    ⟨store, default, quick, persist⟩) default with
  | (.error e, _) => return .error e
  | (.ok hs, stt) => return .ok (stt, hs)

end Yatima.Commit
