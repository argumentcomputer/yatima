import Yatima.Compiler.Printing
import Yatima.Ipld.ToIpld
import YatimaStdLib.RBMap

import Lean

namespace Yatima.Compiler

open Std (RBMap)

instance : Coe Lean.BinderInfo BinderInfo where coe
  | .default        => .default
  | .auxDecl        => .auxDecl
  | .instImplicit   => .instImplicit
  | .strictImplicit => .strictImplicit
  | .implicit       => .implicit

instance : Coe Lean.Literal Literal where coe
  | .natVal n => .nat n
  | .strVal s => .str s

instance : Coe Lean.DefinitionSafety DefinitionSafety where coe
  | .safe    => .safe
  | .unsafe  => .unsafe
  | .partial => .partial

instance : Coe Lean.QuotKind QuotKind where coe
  | .type => .type
  | .ind  => .ind
  | .lift => .lift
  | .ctor => .ctor

open ToIpld

def derefConst (idx : ConstIdx) : CompileM Const := do
  let defns := (← get).defns
  let size := defns.size
  if h : idx < size then
    return defns[idx]'h
  else
    throw $ .invalidDereferringIndex idx size

def findConstant (name : Lean.Name) : CompileM Lean.ConstantInfo := do
  match (← read).constMap.find? name with
  | some const => pure const
  | none => throw $ .unknownConstant name

def toYatimaUniv (l : Lean.Level) : CompileM (UnivCid × Univ) := do
  let (value, univ) ← match l with
    | .zero      => do
      let value : Ipld.Both Ipld.Univ := ⟨ .zero, .zero ⟩
      pure (value, .zero)
    | .succ n    => do
      let (univCid, univ) ← toYatimaUniv n
      let value : Ipld.Both Ipld.Univ := ⟨ .succ univCid.anon, .succ univCid.meta ⟩
      pure (value, .succ univ)
    | .max  a b  => do
      let (univACid, univA) ← toYatimaUniv a
      let (univBCid, univB) ← toYatimaUniv b
      let value : Ipld.Both Ipld.Univ := ⟨ .max univACid.anon univBCid.anon, .max univACid.meta univBCid.meta ⟩
      pure (value, .max univA univB)
    | .imax  a b  => do
      let (univACid, univA) ← toYatimaUniv a
      let (univBCid, univB) ← toYatimaUniv b
      let value : Ipld.Both Ipld.Univ := ⟨ .imax univACid.anon univBCid.anon, .imax univACid.meta univBCid.meta ⟩
      pure (value, .imax univA univB)
    | .param name => do
      let lvls := (← read).univCtx
      match lvls.indexOf? name with
      | some n =>
        let value : Ipld.Both Ipld.Univ := ⟨ .var () n, .var name () ⟩
        pure (value, .var name n)
      | none   => throw $ .levelNotFound name lvls
    | .mvar .. => throw $ .unfilledLevelMetavariable l
  let cid ← StoreValue.insert $ .univ value
  pure (cid, univ)

instance : HMul Ordering Ordering Ordering where
  hMul
  | .gt, _ => .gt
  | .lt, _ => .lt
  | .eq, x => x

def concatOrds : List Ordering -> Ordering :=
  List.foldl (fun x y => x * y) .eq

def cmpLevel (x : Lean.Level) (y : Lean.Level) : (CompileM Ordering) := do
  match x, y with
  | .mvar .., _ => throw $ .unfilledLevelMetavariable x
  | _, .mvar .. => throw $ .unfilledLevelMetavariable y
  | .zero, .zero => return .eq
  | .zero, _ => return .lt
  | _, .zero => return .gt
  | .succ x, .succ y => cmpLevel x y
  | .succ .., _ => return .lt
  | _, .succ .. => return .gt
  | .max lx ly, .max rx ry => (· * ·) <$> cmpLevel lx rx <*> cmpLevel ly ry
  | .max .., _ => return .lt
  | _, .max .. => return .gt
  | .imax lx ly, .imax rx ry => (· * ·) <$> cmpLevel lx rx <*> cmpLevel ly ry
  | .imax .., _ => return .lt
  | _, .imax .. => return .gt
  | .param x, .param y => do
    let lvls := (← read).univCtx
    match (lvls.indexOf? x), (lvls.indexOf? y) with
    | some xi, some yi => return (compare xi yi)
    | none,    _       => throw $ .levelNotFound x lvls
    | _,       none    => throw $ .levelNotFound y lvls

mutual
  /--
  Process a Lean constant into a Yatima constant, returning both the Yatima
  constant and its cid.

  Different behavior is taken if the input `leanConst` is in a mutual block,
  since `toYatimaConst` returns the constant of the entire block (see
  `toYatimaConst`). We avoid returning the entire block and return the `mutDef`
  corresponding the input.

  Side effects: caches any new processed values in `cache`, `expr_cache`, and
  `const_cache`.
  -/
  partial def processYatimaConst (const : Lean.ConstantInfo) :
      CompileM $ ConstCid × ConstIdx := do
    let name := const.name
    let log  := (← read).log
    match (← get).cache.find? name with
    | some c => pure c
    | none   =>
      if log then
        IO.println s!"↡ Stacking {name}{const.formatAll}"
      let c ← toYatimaConst const
      if log then
        IO.println s!"↟ Popping  {name}"
      return c

  partial def toYatimaConst : Lean.ConstantInfo → CompileM (ConstCid × ConstIdx)
  -- These cases add multiple constants at the same time
  | .inductInfo struct => withResetCompileEnv struct.levelParams $ toYatimaInductive struct
  | .defnInfo struct => withResetCompileEnv struct.levelParams $ toYatimaDef struct
  -- These cases are subsumed by the inductive case
  | .ctorInfo struct => do
    match ← findConstant struct.induct with
    | .inductInfo ind => processYatimaConst (.inductInfo ind)
    | const => throw $ .invalidConstantKind const "inductive"
    processYatimaConst (.ctorInfo struct)
  | .recInfo struct => do
    match ← findConstant struct.getInduct with
    | .inductInfo ind => processYatimaConst (.inductInfo ind)
    | const => throw $ .invalidConstantKind const "inductive"
    processYatimaConst (.recInfo struct)
  -- The rest adds the constants to the cache one by one
  | const => withResetCompileEnv const.levelParams do
    -- It is important to push first with some value so we don't lose the position of the constant in a recursive call
    let constIdx ← modifyGet (fun stt => (stt.defns.size, { stt with defns := stt.defns.push default }))
    let values : Ipld.Both Ipld.Const × Const ← match const with
      | .axiomInfo struct =>
        let (typeCid, type) ← toYatimaExpr struct.type
        let ax := {
          name := struct.name
          lvls := struct.levelParams
          type := type
          safe := not struct.isUnsafe }
        let value := ⟨ .axiom $ ax.toIpld typeCid, .axiom $ ax.toIpld typeCid ⟩
        pure (value, .axiom ax)
      | .thmInfo struct =>
        let (typeCid, type) ← toYatimaExpr struct.type
        -- Theorems are never truly recursive, though they can use recursive schemes
        let (valueCid, value) ← toYatimaExpr struct.value
        let thm := {
          name  := struct.name
          lvls  := struct.levelParams
          type  := type
          value := value }
        let value := ⟨.theorem $ thm.toIpld typeCid valueCid, .theorem $ thm.toIpld typeCid valueCid⟩
        pure (value, Const.theorem thm)
      | .opaqueInfo struct =>
        let (typeCid, type) ← toYatimaExpr struct.type
        -- TODO: Is `RBMap.single` correct? Shouldn't we add a new entry to the underlying `recrCtx`?
        let (valueCid, value) ← withRecrs (RBMap.single struct.name (0, constIdx)) $ toYatimaExpr struct.value
        let opaq := {
          name  := struct.name
          lvls  := struct.levelParams
          type  := type
          value := value
          safe  := not struct.isUnsafe }
          let value := ⟨.opaque $ opaq.toIpld typeCid valueCid, .opaque $ opaq.toIpld typeCid valueCid⟩
        pure (value, .opaque opaq)
      | .quotInfo struct =>
        let (typeCid, type) ← toYatimaExpr struct.type
        let quot := {
          name := struct.name
          lvls := struct.levelParams
          type := type
          kind := struct.kind }
        let value := ⟨.quotient $ quot.toIpld typeCid, .quotient $ quot.toIpld typeCid⟩
        pure (value, .quotient quot)
      | _ => unreachable!
    let cid ← StoreValue.insert $ .const values.fst
    addToDefns constIdx values.snd
    addToCache const.name (cid, constIdx)
    pure (cid, constIdx)

  partial def toYatimaExpr : Lean.Expr → CompileM (ExprCid × Expr)
  | .mdata _ e => toYatimaExpr e
  | expr => do
    let (value, expr) ← match expr with
      | .bvar idx => do
        let name ← match (← read).bindCtx.get? idx with
        | some name =>
          let value : Ipld.Both Ipld.Expr := ⟨ .var () idx, .var name () ⟩
          pure (value, .var name idx)
        | none => throw $ .invalidBVarIndex idx
      | .sort lvl => do
        let (univCid, univ) ← toYatimaUniv lvl
        let value : Ipld.Both Ipld.Expr := ⟨ .sort univCid.anon, .sort univCid.meta ⟩
        pure (value, .sort univ)
      | .const name lvls => do
        let pairs ← lvls.mapM $ toYatimaUniv
        let (univCids, univs) ← pairs.foldrM (fun pair pairs => pure (pair.fst :: pairs.fst, pair.snd :: pairs.snd)) ([], [])
        match (← read).recrCtx.find? name with
          | some (i, ref) =>
            let idx := (← read).bindCtx.length + i
            let value : Ipld.Both Ipld.Expr := ⟨ .var () idx, .var name () ⟩
            pure (value, .const name ref univs)
          | none   => do
            let const ← findConstant name
            let (constCid, const) ← processYatimaConst const
            let value : Ipld.Both Ipld.Expr := ⟨ .const () constCid.anon $ univCids.map (·.anon)
                       , .const name constCid.meta $ univCids.map (·.meta) ⟩
            pure (value, .const name const univs)
      | .app fnc arg => do
        let (fncCid, fnc) ← toYatimaExpr fnc
        let (argCid, arg) ← toYatimaExpr arg
        let value : Ipld.Both Ipld.Expr := ⟨ .app fncCid.anon argCid.anon, .app fncCid.meta argCid.meta ⟩
        pure (value, .app fnc arg)
      | .lam name typ bod bnd =>
        let (typCid, typ) ← toYatimaExpr typ
        let (bodCid, bod) ← withName name $ toYatimaExpr bod
        let value : Ipld.Both Ipld.Expr := ⟨ .lam () bnd typCid.anon bodCid.anon, .lam name () typCid.meta bodCid.meta ⟩
        pure (value, .lam name bnd typ bod)
      | .forallE name dom img bnd =>
        let (domCid, dom) ← toYatimaExpr dom
        let (imgCid, img) ← withName name $ toYatimaExpr img
        let value : Ipld.Both Ipld.Expr := ⟨ .pi () bnd domCid.anon imgCid.anon, .pi name () domCid.meta imgCid.meta ⟩
        pure (value, .pi name bnd dom img)
      | .letE name typ exp bod _ =>
        let (typCid, typ) ← toYatimaExpr typ
        let (expCid, exp) ← toYatimaExpr exp
        let (bodCid, bod) ← withName name $ toYatimaExpr bod
        let value : Ipld.Both Ipld.Expr := ⟨ .letE () typCid.anon expCid.anon bodCid.anon, .letE name typCid.meta expCid.meta bodCid.meta ⟩
        pure (value, .letE name typ exp bod)
      | .lit lit=>
        let value : Ipld.Both Ipld.Expr := ⟨ .lit lit, .lit () ⟩
        pure (value, .lit lit)
      | .proj _ idx exp=> do
        let (expCid, exp) ← toYatimaExpr exp
        let value : Ipld.Both Ipld.Expr := ⟨ .proj idx expCid.anon, .proj () expCid.meta ⟩
        pure (value, .proj idx exp)
      | .fvar .. => throw $ .freeVariableExpr expr
      | .mvar .. => throw $ .metaVariableExpr expr
      | .mdata .. => throw $ .metaDataExpr expr
    let cid ← StoreValue.insert $ .expr value
    pure (cid, expr)

  partial def toYatimaInductive (initInd : Lean.InductiveVal) : CompileM (ConstCid × ConstIdx) := do
    -- `constList` is the list of the names of all constants associated with an inductive block: the inductives themselves,
    -- the constructors and the recursors.
    let mut constList : List Lean.Name := []
    for indName in initInd.all do
      match ← findConstant indName with
      | .inductInfo ind =>
        let leanRecs := (← read).constMap.childrenOfWith ind.name -- reverses once
          fun c => match c with | .recInfo _ => true | _ => false
        let leanRecs := leanRecs.map (·.name)
        let addList := (indName :: ind.ctors).append leanRecs
        constList := constList.append addList
      | const => throw $ .invalidConstantKind const "inductive"

    -- All inductives, constructors and recursors are done in one go, so we must append an array of `constList.length` to `defns`
    -- and save the mapping of all names in `constList` to their respective indices
    let mut firstIdx ← modifyGet (fun stt => (stt.defns.size, { stt with defns := stt.defns.append (mkArray constList.length default) }))
    let mut mutualIdxs : RBMap Lean.Name (Nat × Nat) compare := RBMap.empty
    for (i, n) in constList.enum do
      mutualIdxs := mutualIdxs.insert n (i, firstIdx + i)

    -- This part will build the inductive block and add all inductives, constructors and recursors to `defns`
    let indInfos : List (Ipld.Both Ipld.Inductive) ← initInd.all.foldrM (init := []) fun name acc => do
      match ← findConstant name with
      | .inductInfo ind => do
        withRecrs mutualIdxs do
          let ipldInd ← toYatimaIpldInductive ind
          pure $ ipldInd :: acc
      | const => throw $ .invalidConstantKind const "inductive"
    let indBlock := ⟨.mutIndBlock $ indInfos.map (·.anon), .mutIndBlock $ indInfos.map (·.meta)⟩
    let indBlockCid ← StoreValue.insert $ .const indBlock

    let mut ret? : Option (ConstCid × ConstIdx) := none
    let mut defnIdx := firstIdx

    for (indIdx, ⟨indAnon, indMeta⟩) in indInfos.enum do
      -- Add the IPLD inductive projections and inductives to the cache
      let name := indMeta.name.proj₂
      let indProj :=
        ⟨ .inductiveProj ⟨ (), indAnon.lvls, indAnon.type, indBlockCid.anon, indIdx ⟩
        , .inductiveProj ⟨ indMeta.name, indMeta.lvls, indMeta.type, indBlockCid.meta, () ⟩ ⟩
      let cid ← StoreValue.insert $ .const indProj
      addToCache name (cid, defnIdx)
      if name == initInd.name then ret? := some (cid, indIdx)
      defnIdx := defnIdx + 1

      for (ctorIdx, (ctorAnon, ctorMeta)) in (indAnon.ctors.zip indMeta.ctors).enum do
        -- Add the IPLD constructor projections and constructors to the cache
        let name := ctorMeta.name.proj₂
        let ctorProj :=
          ⟨ .constructorProj ⟨ (), ctorAnon.lvls, ctorAnon.type, indBlockCid.anon, indIdx, ctorIdx ⟩
          , .constructorProj ⟨ ctorMeta.name, ctorMeta.lvls, ctorMeta.type, indBlockCid.meta, (), () ⟩ ⟩
        let cid ← StoreValue.insert $ .const ctorProj
        addToCache name (cid, defnIdx)
        defnIdx := defnIdx + 1

      for (recrIdx, (recrAnon, recrMeta)) in (indAnon.recrs.zip indMeta.recrs).enum do
        -- Add the IPLD recursor projections and recursors to the cache
        let name := recrMeta.2.name.proj₂
        let recrProj :=
          ⟨ .recursorProj ⟨ (), recrAnon.2.lvls, recrAnon.2.type, indBlockCid.anon, indIdx, recrIdx ⟩
          , .recursorProj ⟨ recrMeta.2.name, recrMeta.2.lvls, recrMeta.2.type, indBlockCid.meta, (), () ⟩ ⟩
        let cid ← StoreValue.insert $ .const recrProj
        addToCache name (cid, defnIdx)
        defnIdx := defnIdx + 1

    match ret? with
    | some ret => return ret
    | none => throw $ .constantNotCompiled initInd.name

  partial def toYatimaIpldInductive (ind : Lean.InductiveVal) :
      CompileM $ Ipld.Both Ipld.Inductive := do
    let leanRecs := (← read).constMap.childrenOfWith ind.name
      fun c => match c with | .recInfo _ => true | _ => false
    let (recs, ctors) : ((List $ Ipld.Both (Sigma fun x => Ipld.Recursor x ·)) × (List $ Ipld.Both Ipld.Constructor)) :=
      ← leanRecs.foldrM (init := ([], [])) fun r (recs, ctors) =>
        match r with
        | .recInfo rv => do
          if ← isInternalRec rv.type ind.name then do
            let (thisRec, thisCtors) := ← toYatimaIpldInternalRec ind.ctors r
            let recs := (⟨Sigma.mk .Intr thisRec.anon, Sigma.mk .Intr thisRec.meta⟩) :: recs
            return (recs, thisCtors)
          else do
            let thisRec := ← toYatimaIpldExternalRec r
            let recs := (⟨Sigma.mk .Extr thisRec.anon, Sigma.mk .Extr thisRec.meta⟩) :: recs
            return (recs, ctors)
        | _ => throw $ .nonRecursorExtractedFromChildren r.name
    let (typeCid, type) ← toYatimaExpr ind.type
    let struct ← if ind.isRec || ind.numIndices != 0 then pure none else
      match ind.ctors with
      | [ctor] => do
        let some (_, ctorIdx) := (← read).recrCtx.find? ctor | throw $ .unknownConstant ctor
        match ← derefConst ctorIdx with
        | .constructor ctor => pure $ some ctor
        | const => throw $ .invalidConstantKind' const "constructor"
      | _ => pure none
    let unit := match struct with
      | some ctor => ctor.fields == 0
      | none => false
    let tcInd := .inductive {
      name    := ind.name
      lvls    := ind.levelParams
      type    := type
      params  := ind.numParams
      indices := ind.numIndices
      recr    := ind.isRec
      safe    := not ind.isUnsafe
      refl    := ind.isReflexive
      unit    := unit
      struct  := struct
    }
    let some (_, defnIdx) := (← read).recrCtx.find? ind.name | throw $ .unknownConstant ind.name
    addToDefns defnIdx tcInd
    return {
      anon := ⟨ ()
        , ind.levelParams.length
        , typeCid.anon
        , ind.numParams
        , ind.numIndices
        , ctors.map (·.anon)
        , recs.map (·.anon)
        , ind.isRec
        , not ind.isUnsafe
        , ind.isReflexive ⟩
      meta := ⟨ ind.name
        , ind.levelParams
        , typeCid.meta
        , () , ()
        , ctors.map (·.meta)
        , recs.map (·.meta)
        , () , () , () ⟩
    }

  partial def isInternalRec (expr : Lean.Expr) (name : Lean.Name) : CompileM Bool :=
    match expr with
      | .forallE _ t e _  => match e with
        | .forallE ..  => isInternalRec e name
        -- t is the major premise
        | _ => isInternalRec t name
      | .app e .. => isInternalRec e name
      | .const n .. => return n == name
      | _ => return false

  partial def toYatimaIpldInternalRec (ctors : List Lean.Name) :
      Lean.ConstantInfo → CompileM
        (Ipld.Both (Ipld.Recursor .Intr) × (List $ Ipld.Both Ipld.Constructor))
    | .recInfo rec => do
      withLevels rec.levelParams do
        let (typeCid, type) ← toYatimaExpr rec.type
        let ctorMap : RBMap Name (Ipld.Both Ipld.Constructor) compare ← rec.rules.foldlM
          (init := .empty) fun ctorMap r => do
            match ctors.indexOf? r.ctor with
            | some _ =>
              let ctor ← toYatimaConstructor r
              return ctorMap.insert ctor.meta.name.proj₂ ctor
            -- this is an external recursor rule
            | none => return ctorMap
        let retCtors ← ctors.mapM fun ctor => do
          match ctorMap.find? ctor with
          | some thisCtor => pure thisCtor
          | none => throw $ .unknownConstant ctor
        let tcRecr : Const := .intRecursor {
          name    := rec.name
          lvls    := rec.levelParams
          type    := type
          params  := rec.numParams
          indices := rec.numIndices
          motives := rec.numMotives
          minors  := rec.numMinors
          k       := rec.k }
        let some (_, defnIdx) := (← read).recrCtx.find? rec.name | throw $ .unknownConstant rec.name
        addToDefns defnIdx tcRecr
        let recr := ⟨
          { name    := ()
            lvls    := rec.levelParams.length
            type    := typeCid.anon
            params  := rec.numParams
            indices := rec.numIndices
            motives := rec.numMotives
            minors  := rec.numMinors
            rules   := ()
            k       := rec.k },
          { name    := rec.name
            lvls    := rec.levelParams
            type    := typeCid.meta
            params  := ()
            indices := ()
            motives := ()
            minors  := ()
            rules   := ()
            k       := () } ⟩
        return (recr, retCtors)
    | const => throw $ .invalidConstantKind const "recursor"

  partial def toYatimaConstructor (rule : Lean.RecursorRule) : CompileM $ Ipld.Both Ipld.Constructor := do
      let (rhsCid, rhs) ← toYatimaExpr rule.rhs
      match ← findConstant rule.ctor with
      | .ctorInfo ctor =>
        let (typeCid, type) ← toYatimaExpr ctor.type
        let tcCtor : Const := .constructor {
          name    := ctor.name
          lvls    := ctor.levelParams
          type    := type
          idx     := ctor.cidx
          params  := ctor.numParams
          fields  := ctor.numFields
          rhs     := rhs
          safe    := not ctor.isUnsafe
        }
        let some (_, defnIdx) := (← read).recrCtx.find? ctor.name | throw $ .unknownConstant ctor.name
        addToDefns defnIdx tcCtor
        return ⟨
          { rhs    := rhsCid.anon
            lvls   := ctor.levelParams.length
            name   := ()
            type   := typeCid.anon
            idx    := ctor.cidx
            params := ctor.numParams
            fields := ctor.numFields
            safe   := not ctor.isUnsafe },
          { rhs    := rhsCid.meta
            lvls   := ctor.levelParams
            name   := ctor.name
            type   := typeCid.meta
            idx    := ()
            params := ()
            fields := ()
            safe   := () } ⟩
      | const => throw $ .invalidConstantKind const "constructor"

  partial def toYatimaIpldExternalRec :
      Lean.ConstantInfo → CompileM (Ipld.Both (Ipld.Recursor .Extr))
    | .recInfo rec => do
      withLevels rec.levelParams do
        let (typeCid, type) ← toYatimaExpr rec.type
        let (rules, tcRules) : Ipld.Both (fun k => List $ Ipld.RecursorRule k) × List RecursorRule := ← rec.rules.foldlM
          (init := (⟨[], []⟩, [])) fun rules r => do
            let (recrRule, tcRecrRule) ← toYatimaExternalRecRule r
            return (⟨recrRule.anon::rules.1.anon, recrRule.meta::rules.1.meta⟩, tcRecrRule::rules.2)
        let tcRecr : Const := .extRecursor {
          name    := rec.name
          lvls    := rec.levelParams
          type    := type
          params  := rec.numParams
          indices := rec.numIndices
          motives := rec.numMotives
          minors  := rec.numMinors
          rules   := tcRules
          k       := rec.k
        }
        let some (_, defnIdx) := (← read).recrCtx.find? rec.name | throw $ .unknownConstant rec.name
        addToDefns defnIdx tcRecr
        return ⟨
          { name    := ()
            lvls    := rec.levelParams.length
            type    := typeCid.anon
            params  := rec.numParams
            indices := rec.numIndices
            motives := rec.numMotives
            minors  := rec.numMinors
            rules   := rules.anon
            k       := rec.k },
          { name    := rec.name
            lvls    := rec.levelParams
            type    := typeCid.meta
            params  := ()
            indices := ()
            motives := ()
            minors  := ()
            rules   := rules.meta
            k       := () } ⟩
    | const => throw $ .invalidConstantKind const "recursor"
    
  partial def toYatimaExternalRecRule (rule : Lean.RecursorRule) :
      CompileM (Ipld.Both Ipld.RecursorRule × RecursorRule) := do
    let (rhsCid, rhs) ← toYatimaExpr rule.rhs
    let const ← findConstant rule.ctor
    let (ctorCid, ctor?) ← processYatimaConst const
    let ctor ← match ← derefConst ctor? with
      | .constructor ctor => pure ctor
      | const => throw $ .invalidConstantKind' const "constructor"
    let recrRule := ⟨
      { ctor := ctorCid.anon, fields := rule.nfields, rhs := rhsCid.anon },
      { ctor := ctorCid.meta, fields := (), rhs := rhsCid.meta }⟩
    let tcRecrRule := { ctor := ctor, fields := rule.nfields, rhs := rhs }
    return (recrRule, tcRecrRule)

  partial def toYatimaDef (struct : Lean.DefinitionVal) : CompileM (ConstCid × ConstIdx) := do
    if struct.all.length == 1 then
      let constIdx ← modifyGet (fun stt => (stt.defns.size, { stt with defns := stt.defns.push default }))
      let (value, defn) ← withRecrs (RBMap.single struct.name (0, constIdx)) $ toYatimaDefIpld struct
      let cid ← StoreValue.insert $ .const ⟨ .definition value.anon, .definition value.meta ⟩
      addToCache struct.name (cid, constIdx)
      addToDefns constIdx $ .definition defn
      pure (cid, constIdx)
    else
      let mutualDefs ← struct.all.mapM fun name => do
        match ← findConstant name with
        | .defnInfo defn => pure defn
        | const => throw $ .invalidConstantKind const "definition"
      let mutualDefs ← sortDefs [mutualDefs]
      let mutualSize := struct.all.length
      let mut firstIdx ← modifyGet (fun stt => (stt.defns.size, { stt with defns := stt.defns.append (mkArray mutualSize default) }))
      let mut mutualIdxs : RBMap Lean.Name (Nat × Nat) compare := RBMap.empty
      for (i, ds) in mutualDefs.enum do
        for d in ds do
          mutualIdxs := mutualIdxs.insert d.name (i, firstIdx + i)
      let definitions ← withRecrs mutualIdxs $
        mutualDefs.mapM fun ds => ds.mapM $ toYatimaDefIpld
      let definitionsAnon := (definitions.map fun ds => match ds.head? with | some d => [d.1.anon] | none => []).join
      let definitionsMeta := definitions.map fun ds => ds.map $ (·.meta) ∘ Prod.fst
      let block : Ipld.Both Ipld.Const := ⟨ .mutDefBlock definitionsAnon, .mutDefBlock definitionsMeta ⟩
      let blockCid ← StoreValue.insert $ .const block

      let mut ret? : Option (ConstCid × ConstIdx) := none

      for (⟨defnAnon, defnMeta⟩, defn) in definitions.join do
        let some (idx, _) := mutualIdxs.find? defn.name | throw $ .cantFindMutDefIndex defn.name
        let value := ⟨ .definitionProj $ ⟨(), defn.lvls.length, defnAnon.type, blockCid.anon, idx⟩
                     , .definitionProj $ ⟨defn.name, defn.lvls, defnMeta.type, blockCid.meta, ()⟩ ⟩
        let cid ← StoreValue.insert $ .const value
        let constIdx := idx + firstIdx
        addToDefns constIdx $ .definition defn
        addToCache defn.name (cid, constIdx)
        if defn.name == struct.name then ret? := some (cid, constIdx)

      match ret? with
      | some ret => return ret
      | none => throw $ .constantNotCompiled struct.name

  partial def toYatimaDefIpld (defn : Lean.DefinitionVal) :
      CompileM (Ipld.Both Ipld.Definition × Definition) := do
    let (typeCid, type) ← toYatimaExpr defn.type
    let (valueCid, value) ← toYatimaExpr defn.value
    let defn := {
      name   := defn.name
      lvls   := defn.levelParams
      type
      value
      safety := defn.safety }
    return (⟨defn.toIpld typeCid valueCid, defn.toIpld typeCid valueCid⟩, defn)

  partial def cmpExpr (names : Std.RBMap Lean.Name Nat compare) :
      Lean.Expr → Lean.Expr → CompileM Ordering
    | e@(.mvar ..), _ => throw $ .unfilledExprMetavariable e
    | _, e@(.mvar ..) => throw $ .unfilledExprMetavariable e
    | e@(.fvar ..), _ => throw $ .freeVariableExpr e
    | _, e@(.fvar ..) => throw $ .freeVariableExpr e
    | .mdata _ x, .mdata _ y  => cmpExpr names x y
    | .mdata _ x, y  => cmpExpr names x y
    | x, .mdata _ y  => cmpExpr names x y
    | .bvar x, .bvar y => return (compare x y)
    | .bvar .., _ => return .lt
    | _, .bvar .. => return .gt
    | .sort x, .sort y => cmpLevel x y
    | .sort .., _ => return .lt
    | _, .sort .. => return .gt
    | .const x xls, .const y yls => do
      let univs ← concatOrds <$> (List.zip xls yls).mapM (fun (x,y) => cmpLevel x y)
      if univs != .eq then return univs
      match names.find? x, names.find? y with
      | some nx, some ny => return compare nx ny
      | none, some _ => return .gt
      | some _, none => return .lt
      | none, none => do
        let xCid := (← processYatimaConst (← findConstant x)).fst
        let yCid := (← processYatimaConst (← findConstant y)).fst
        return (compare xCid.anon yCid.anon)
    | .const .., _ => return .lt
    | _, .const .. => return .gt
    | .app xf xa, .app yf ya => (· * ·) <$> cmpExpr names xf yf <*> cmpExpr names xa ya
    | .app .., _ => return .lt
    | _, .app .. => return .gt
    | .lam _ xt xb _, .lam _ yt yb _ => (· * ·) <$> cmpExpr names xt yt <*> cmpExpr names xb yb
    | .lam .., _ => return .lt
    | _, .lam .. => return .gt
    | .forallE _ xt xb _, .forallE _ yt yb _ => (· * ·) <$> cmpExpr names xt yt <*> cmpExpr names xb yb
    | .forallE .., _ => return .lt
    | _, .forallE .. => return .gt
    | .letE _ xt xv xb _, .letE _ yt yv yb _ => (· * · * ·) <$> cmpExpr names xt yt <*> cmpExpr names xv yv <*> cmpExpr names xb yb
    | .letE .., _ => return .lt
    | _, .letE .. => return .gt
    | .lit x, .lit y =>
      return if x < y then .lt else if x == y then .eq else .gt
    | .lit .., _ => return .lt
    | _, .lit .. => return .gt
    | .proj _ nx tx, .proj _ ny ty => do
      let ts ← cmpExpr names tx ty
      return concatOrds [compare nx ny, ts]

  partial def cmpDef (names : Std.RBMap Lean.Name Nat compare)
    (x : Lean.DefinitionVal) (y : Lean.DefinitionVal) :
      CompileM Ordering := do
    let ls := compare x.levelParams.length y.levelParams.length
    let ts ← cmpExpr names x.type y.type
    let vs ← cmpExpr names x.value y.value
    return concatOrds [ls, ts, vs]

  partial def eqDef (names : Std.RBMap Lean.Name Nat compare)
    (x : Lean.DefinitionVal) (y : Lean.DefinitionVal) :
      CompileM Bool := do
    match (← cmpDef names x y) with
      | .eq => pure true
      | _ => pure false

  /-- todo -/
  partial def sortDefs (dss : List (List Lean.DefinitionVal)) :
      CompileM (List (List Lean.DefinitionVal)) := do
    let enum (ll : List (List Lean.DefinitionVal)) :=
      Std.RBMap.ofList (ll.enum.map fun (n, xs) => xs.map (·.name, n)).join
    let names := enum dss
    let newDss ← (← dss.mapM fun ds =>
      match ds with
      | []  => unreachable!
      | [d] => return [[d]]
      | ds  => return (← List.groupByM (eqDef names) $
        ← ds.sortByM (cmpDef names))).joinM

    -- must normalize, see comments
    let normDss    := dss.map    fun ds => ds.map (·.name) |>.sort
    let normNewDss := newDss.map fun ds => ds.map (·.name) |>.sort
    if normDss == normNewDss then
      return newDss
    else
      sortDefs newDss

end

def compileM (constMap : Lean.ConstMap) : CompileM Unit := do
  let log := (← read).log
  constMap.forM fun _ const => do
    let (_, c) ← processYatimaConst const
    if log then
      IO.println "\n========================================="
      IO.println    const.name
      IO.println   "========================================="
      IO.println s!"{PrintLean.printLeanConst const}"
      IO.println   "========================================="
      IO.println s!"{← PrintYatima.printYatimaConst (← derefConst c)}"
      IO.println   "=========================================\n"

def compile (filePath : System.FilePath) (log : Bool := false)
    (stt : CompileState := default) : IO $ Except CompileError CompileState := do
  let filePathStr := filePath.toString
  match ← Lean.runFrontend (← IO.FS.readFile filePath) filePathStr with
  | (some err, _) => return .error $ .errorsOnFile filePathStr err
  | (none, env) =>
    -- building an environment `env₀` just with the imports from `filePath`
    let importFile := env.header.imports.map (·.module) |>.foldl
      (init := "prelude\n")
      fun acc m => s!"{acc}import {m}\n"
    let (_, env₀) ← Lean.runFrontend importFile

    -- filtering out open references
    let map  := Lean.filterConstants env.constants
    let map₀ := Lean.filterConstants env₀.constants

    -- computing `delta`, which is what `map` adds in w.r.t. `map₀`
    let delta : Lean.ConstMap := map.fold
      (init := Lean.SMap.empty) fun acc n c =>
        match map₀.find? n with
        | some c' => if c == c' then acc else acc.insert n c
        | none    => acc.insert n c

    -- triggering compilation
    CompileM.run (.init map log) stt (compileM delta)

/--
This function must be called before `compile` if the file to be compiled has
imports (the automatic imports from `Init` also count).
-/
def setLibsPaths : IO Unit := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["print-paths"]
  }
  let split := out.stdout.splitOn "\"oleanPath\":[" |>.getD 1 ""
  let split := split.splitOn "],\"loadDynlibPaths\":[" |>.getD 0 ""
  let paths := split.replace "\"" "" |>.splitOn ","|>.map System.FilePath.mk
  Lean.initSearchPath (← Lean.findSysroot) paths

end Yatima.Compiler
