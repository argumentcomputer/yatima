import Yatima.Commit.CommitM
import Yatima.Commit.ToLDON
import Yatima.ContAddr.LightData

namespace Yatima.Commit

open IR TC Lurk

partial def mkTCUniv (hash : Hash) : CommitM Univ := do
  match (← get).univ.find? hash with
  | some u => pure u
  | none =>
    let u ← match (← read).univ.find? hash with
      | none => throw sorry
      | some .zero => pure .zero
      | some $ .succ u => pure $ .succ (← mkTCUniv u)
      | some $ .max u v => pure $ .max (← mkTCUniv u) (← mkTCUniv v)
      | some $ .imax u v => pure $ .imax (← mkTCUniv u) (← mkTCUniv v)
      | some $ .var n => pure $ .var n
    -- persistData (hash, u) UNIVDIR
    modifyGet fun stt => (u, { stt with univ := stt.univ.insert hash u })

mutual

partial def mkTCExpr (hash : Hash) : CommitM Expr := do
  match (← get).expr.find? hash with
  | some e => pure e
  | none =>
    let e ← match (← read).expr.find? hash with
      | none => throw sorry
      | some $ .var i us => sorry
      | some $ .sort u => pure $ .sort (← mkTCUniv u)
      | some $ .const c us =>
        pure $ .const (← commitConst c) (← us.mapM mkTCUniv)
      | some $ .app x y => pure $ .app (← mkTCExpr x) (← mkTCExpr y)
      | some $ .lam x y => pure $ .lam (← mkTCExpr x) (← mkTCExpr y)
      | some $ .pi  x y => pure $ .pi  (← mkTCExpr x) (← mkTCExpr y)
      | some $ .letE x y z => pure $ .letE (← mkTCExpr x) (← mkTCExpr y) (← mkTCExpr z)
      | some $ .lit l => pure $ .lit l
      | some $ .proj n e => pure $ .proj n (← mkTCExpr e)
    -- persistData (hash, e) EXPRDIR
    modifyGet fun stt => (e, { stt with expr := stt.expr.insert hash e })

partial def mkTCCtor : IR.ConstructorAnon → CommitM Constructor
  | ⟨lvls, typeHash, ids, params, fields, safe⟩ =>
    return ⟨lvls, ← mkTCExpr typeHash, ids, params, fields, safe⟩

partial def mkTCInd : IR.InductiveAnon → CommitM Inductive
  | ⟨lvls, type, params, indices, ctors, _, recr, safe, refl⟩ => do
    -- Structures can't be recursive nor have indices
    let (struct, unit) ← if recr || indices != 0 then pure (none, false) else
      match ctors with
      -- Structures can only have one constructor
      | [ctor] => do
        let f ← commitConst (ctor : LightData).hash
        pure $ (some f, ctor.fields == 0)
      | _ => pure (none, false)
    return ⟨lvls, ← mkTCExpr type, params, indices, ← ctors.mapM mkTCCtor, recr,
      safe, refl, struct, unit⟩

partial def mkTCConst (hash : Hash) : CommitM Const := do
  match (← get).const.find? hash with
  | some c => pure c
  | none =>
    let c ← match (← read).const.find? hash with
      | none => throw sorry
      | some $ .axiom x => pure $ .axiom ⟨x.lvls, ← mkTCExpr x.type, x.safe⟩
      | some $ .theorem x => pure $ .theorem ⟨x.lvls, ← mkTCExpr x.type, ← mkTCExpr x.value⟩
      | some $ .opaque x => pure $ .opaque ⟨x.lvls, ← mkTCExpr x.type, ← mkTCExpr x.value, x.safe⟩
      | some $ .quotient x => pure $ .quotient ⟨x.lvls, ← mkTCExpr x.type, x.kind⟩
      | some $ .inductiveProj x =>
        match (← read).const.find? x.block with
        | none => throw sorry
        | some $ .mutIndBlock inds =>
          let some ind := inds.get? x.idx | throw sorry
          pure $ .inductive $ ← mkTCInd ind
        | _ => throw sorry
      | some $ .constructorProj x =>
        match (← read).const.find? x.block with
        | none => throw sorry
        | some $ .mutIndBlock inds =>
          let some ind := inds.get? x.idx | throw sorry
          let some ⟨lvls, type, idx, params, fields, safe⟩ := ind.ctors.get? x.idx | throw sorry
          pure $ .constructor ⟨lvls, ← mkTCExpr type, idx, params, fields, safe⟩
        | _ => throw sorry
      | some $ .recursorProj x =>
        match (← read).const.find? x.block with
        | none => throw sorry
        | some $ .mutIndBlock inds =>
          let some ind := inds.get? x.idx | throw sorry
          let indF ← commitConst (ind : LightData).hash
          let some ⟨lvls, type, params, indices, motives, minors, rules, isK, internal⟩ := ind.recrs.get? x.idx | throw sorry
          pure $ .recursor ⟨lvls, ← mkTCExpr type, params, indices, motives, minors, sorry, isK, internal, indF, sorry⟩
        | _ => throw sorry
      | some $ .definitionProj x =>
        match (← read).const.find? x.block with
        | none => throw sorry
        | some $ .mutDefBlock defs =>
          let some ⟨lvls, type, value, safety⟩ := defs.get? x.idx | throw sorry
          pure $ .definition ⟨lvls, ← mkTCExpr type, ← mkTCExpr value, safety, sorry⟩
        | _ => throw sorry
      | some $ .mutDefBlock _ | some $ .mutIndBlock _ => throw sorry
    -- persistData (hash, c) CONSTDIR
    modifyGet fun stt => (c, { stt with const := stt.const.insert hash c })

partial def commitConst (hash : Hash) : CommitM F := do
  match (← get).commits.find? hash with
  | some f => pure f
  | none =>
    let const ← mkTCConst hash
    let ldon := const.toLDON
    -- this is expensive
    let (f, encStt) := ldon |>.commit (← get).ldonHashState
    modifyGet fun stt => (f, { stt with
      commits := stt.commits.insert hash f
      ldonHashState := encStt })

end

def commitM (hashes : Array Hash) : CommitM $ Array F :=
  hashes.mapM commitConst

def commit (hashes : Array Hash) (store : Store) :
    IO $ Except String (Array F) := do
  match ← StateT.run (ReaderT.run (commitM hashes) store) default with
  | (.error e, _) => return .error e
  | (.ok hs, _) => return .ok hs

end Yatima.Commit
