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
      | none => match (← read).univs.find? hash with
        | none => throw sorry
        | some .zero => pure .zero
        | some $ .succ u => pure $ .succ (← mkUniv u)
        | some $ .max u v => pure $ .max (← mkUniv u) (← mkUniv v)
        | some $ .imax u v => pure $ .imax (← mkUniv u) (← mkUniv v)
        | some $ .var n => pure $ .var n
      dumpData u $ (← get).univPaths.find! hash
    modifyGet fun stt => (u, { stt with univs := stt.univs.insert hash u })

mutual

partial def mkExpr (hash : Hash) : CommitM Expr := do
  match (← get).exprs.find? hash with
  | some e => pure e
  | none =>
    let e ← match ← loadExpr hash with
      | some e => pure e
      | none => match (← read).exprs.find? hash with
        | none => throw sorry
        | some $ .var i us => sorry
        | some $ .sort u => pure $ .sort (← mkUniv u)
        | some $ .const c us => pure $ .const (← commitConst c) (← us.mapM mkUniv)
        | some $ .app x y => pure $ .app (← mkExpr x) (← mkExpr y)
        | some $ .lam x y => pure $ .lam (← mkExpr x) (← mkExpr y)
        | some $ .pi  x y => pure $ .pi  (← mkExpr x) (← mkExpr y)
        | some $ .letE x y z => pure $ .letE (← mkExpr x) (← mkExpr y) (← mkExpr z)
        | some $ .lit l => pure $ .lit l
        | some $ .proj n e => pure $ .proj n (← mkExpr e)
      dumpData e $ (← get).exprPaths.find! hash
    modifyGet fun stt => (e, { stt with exprs := stt.exprs.insert hash e })

partial def mkCtor : IR.ConstructorAnon → CommitM Constructor
  | ⟨lvls, typeHash, ids, params, fields, safe⟩ =>
    return ⟨lvls, ← mkExpr typeHash, ids, params, fields, safe⟩

partial def mkInd : IR.InductiveAnon → CommitM Inductive
  | ⟨lvls, type, params, indices, ctors, _, recr, safe, refl⟩ => do
    -- Structures can't be recursive nor have indices
    let (struct, unit) ← if recr || indices != 0 then pure (none, false) else
      match ctors with
      -- Structures can only have one constructor
      | [ctor] =>
        let f ← commitConst (ctor : LightData).hash -- can we avoid hashing?
        pure $ (some f, ctor.fields == 0)
      | _ => pure (none, false)
    return ⟨lvls, ← mkExpr type, params, indices, ← ctors.mapM mkCtor, recr,
      safe, refl, struct, unit⟩

partial def mkConst (hash : Hash) : CommitM Const := do
  match (← get).consts.find? hash with
  | some c => pure c
  | none =>
    let c ← match ← loadConst hash with
      | some c => pure c
      | none => match (← read).consts.find? hash with
        | none => throw sorry
        | some $ .axiom x => pure $ .axiom ⟨x.lvls, ← mkExpr x.type, x.safe⟩
        | some $ .theorem x => pure $ .theorem ⟨x.lvls, ← mkExpr x.type, ← mkExpr x.value⟩
        | some $ .opaque x => pure $ .opaque ⟨x.lvls, ← mkExpr x.type, ← mkExpr x.value, x.safe⟩
        | some $ .quotient x => pure $ .quotient ⟨x.lvls, ← mkExpr x.type, x.kind⟩
        | some $ .inductiveProj x =>
          match (← read).consts.find? x.block with
          | none => throw sorry
          | some $ .mutIndBlock inds =>
            let some ind := inds.get? x.idx | throw sorry
            pure $ .inductive $ ← mkInd ind
          | _ => throw sorry
        | some $ .constructorProj x =>
          match (← read).consts.find? x.block with
          | none => throw sorry
          | some $ .mutIndBlock inds =>
            let some ind := inds.get? x.idx | throw sorry
            let some ⟨lvls, type, idx, params, fields, safe⟩ := ind.ctors.get? x.idx | throw sorry
            pure $ .constructor ⟨lvls, ← mkExpr type, idx, params, fields, safe⟩
          | _ => throw sorry
        | some $ .recursorProj x =>
          match (← read).consts.find? x.block with
          | none => throw sorry
          | some $ .mutIndBlock inds =>
            let some ind := inds.get? x.idx | throw sorry
            let indF ← commitConst (ind : LightData).hash -- can we avoid hashing?
            let some ⟨lvls, type, params, indices, motives, minors, rules, isK, internal⟩ := ind.recrs.get? x.idx | throw sorry
            pure $ .recursor ⟨lvls, ← mkExpr type, params, indices, motives, minors, sorry, isK, internal, indF, sorry⟩
          | _ => throw sorry
        | some $ .definitionProj x =>
          match (← read).consts.find? x.block with
          | none => throw sorry
          | some $ .mutDefBlock defs =>
            let some ⟨lvls, type, value, safety⟩ := defs.get? x.idx | throw sorry
            pure $ .definition ⟨lvls, ← mkExpr type, ← mkExpr value, safety, sorry⟩
          | _ => throw sorry
        | some $ .mutDefBlock _ | some $ .mutIndBlock _ => throw sorry
      dumpData c $ (← get).constPaths.find! hash
    modifyGet fun stt => (c, { stt with consts := stt.consts.insert hash c })

partial def commitConst (hash : Hash) : CommitM F := do
  match (← get).commits.find? hash with
  | some f => pure f
  | none => match ← loadCommit hash with
    | some f =>
      modifyGet fun stt => (f, {stt with commits := stt.commits.insert hash f})
    | none =>
      let const ← mkConst hash
      let (f, encStt) := const.toLDON.commit (← get).ldonHashState -- expensive
      dumpData f $ (← get).commitPaths.find! hash
      modifyGet fun stt => (f, { stt with
        commits := stt.commits.insert hash f
        ldonHashState := encStt })

end

def commitM (hashes : Array Hash) : CommitM $ Array F := do
  let hashes ← hashes.mapM commitConst
  dumpData (← get).ldonHashState LDONHASHCACHE
  return hashes

def commit (hashes : Array Hash) : IO $ Except String (Array F) := do
  match ← StoreAnon.load hashes with
  | .error e => return .error e
  | .ok store =>
    match ← StateT.run (ReaderT.run (commitM hashes) store) default with
    | (.error e, _) => return .error e
    | (.ok hs, _) => return .ok hs

end Yatima.Commit
