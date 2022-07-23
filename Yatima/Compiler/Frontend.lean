import Yatima.Compiler.Printing
import Yatima.ToIpld
import YatimaStdLib.RBMap

import Lean

namespace Yatima.Compiler

open Std (RBMap)

instance : Coe Lean.Name Name where
  coe := toString

instance : Coe (List Lean.Name) (List Name) where
  coe l := l.map toString

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
  pure $ defns.get! idx

def findConstant (name : Name) : CompileM Lean.ConstantInfo := do
  match (← read).constMap.find? name with
  | some const => pure const
  | none => throw s!"Unknown constant '{name}'"

def toYatimaUniv (l : Lean.Level) : CompileM (UnivCid × Univ) := do
  let (value, univ) ← match l with
    | .zero _      => do
      let value : Ipld.Both Ipld.Univ := ⟨ .zero, .zero ⟩
      pure (value, .zero)
    | .succ n _    => do
      let (univCid, univ) ← toYatimaUniv n
      let value : Ipld.Both Ipld.Univ := ⟨ .succ univCid.anon, .succ univCid.meta ⟩
      pure (value, .succ univ)
    | .max  a b _  => do
      let (univACid, univA) ← toYatimaUniv a
      let (univBCid, univB) ← toYatimaUniv b
      let value : Ipld.Both Ipld.Univ := ⟨ .max univACid.anon univBCid.anon, .max univACid.meta univBCid.meta ⟩
      pure (value, .max univA univB)
    | .imax  a b _  => do
      let (univACid, univA) ← toYatimaUniv a
      let (univBCid, univB) ← toYatimaUniv b
      let value : Ipld.Both Ipld.Univ := ⟨ .imax univACid.anon univBCid.anon, .imax univACid.meta univBCid.meta ⟩
      pure (value, .imax univA univB)
    | .param name _ => do
      let lvls := (← read).univCtx
      match lvls.indexOf? name with
      | some n =>
        let value : Ipld.Both Ipld.Univ := ⟨ .param () n, .param name () ⟩
        pure (value, .param name n)
      | none   => throw s!"'{name}' not found in '{lvls}'"
    | .mvar .. => throw "Unfilled level metavariable"
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
  | .mvar .., _ => throw "Unfilled level metavariable"
  | _, .mvar .. => throw "Unfilled level metavariable"
  | .zero _, .zero _ => return .eq
  | .zero _, _ => return .lt
  | _, .zero _  => return .gt
  | .succ x _, .succ y _ => cmpLevel x y
  | .succ _ _, _ => return .lt
  | _, .succ _ _ => return .gt
  | .max lx ly _, .max rx ry _ => (· * ·) <$> cmpLevel lx rx <*> cmpLevel ly ry
  | .max _ _ _, _ => return .lt
  | _, .max _ _ _ => return .gt
  | .imax lx ly _, .imax rx ry _ => (· * ·) <$> cmpLevel lx rx <*> cmpLevel ly ry
  | .imax _ _ _, _ => return .lt
  | _, .imax _ _ _ => return .gt
  | .param x _, .param y _ => do
    let lvls := (← read).univCtx
    match (lvls.indexOf? x), (lvls.indexOf? y) with
    | some xi, some yi => return (compare xi yi)
    | none, _   => throw s!"'{x}' not found in '{lvls}'"
    | _, none   => throw s!"'{y}' not found in '{lvls}'"

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
    match (← get).cache.find? const.name with
    | some c => pure c
    | none   => toYatimaConst const

  partial def toYatimaConst : Lean.ConstantInfo → CompileM (ConstCid × ConstIdx)
  -- These cases add multiple constants at the same time
  | .inductInfo struct => withResetCompileEnv struct.levelParams $ toYatimaInductive struct
  | .defnInfo struct => withResetCompileEnv struct.levelParams $ toYatimaDef struct
  -- These cases are subsumed by the inductive case
  | .ctorInfo struct => do
    match (← read).constMap.find? struct.induct with
    | some (.inductInfo ind) => processYatimaConst (.inductInfo ind)
    | some const => throw s!"Invalid constant kind for '{const.name}'. Expected 'inductive' but got '{const.ctorName}'"
    | none => throw s!"Unknown constant '{struct.induct}'"
    processYatimaConst (.ctorInfo struct)
  | .recInfo struct => do
    match (← read).constMap.find? struct.getInduct with
    | some (.inductInfo ind) => processYatimaConst (.inductInfo ind)
    | some const => throw s!"Invalid constant kind for '{const.name}'. Expected 'inductive' but got '{const.ctorName}'"
    | none => throw s!"Unknown constant '{struct.getInduct}'"
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
        pure (value, Const.axiom ax)
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
    modify (fun stt => { stt with defns := stt.defns.set! constIdx values.snd })
    addToCache const.name (cid, constIdx)
    pure (cid, constIdx)

  partial def toYatimaExpr : Lean.Expr → CompileM (ExprCid × Expr)
  | .mdata _ e _ => toYatimaExpr e
  | expr => do
    let (value, expr) ← match expr with
      | .bvar idx _ => do
        let name ← match (← read).bindCtx.get? idx with
        | some name =>
          let value : Ipld.Both Ipld.Expr := ⟨ .var () idx, .var name () ⟩
          pure (value, .var name idx)
        | none => throw "Processed bvar has index greater than length of binder context"
      | .sort lvl _ => do
        let (univCid, univ) ← toYatimaUniv lvl
        let value : Ipld.Both Ipld.Expr := ⟨ .sort univCid.anon, .sort univCid.meta ⟩
        pure (value, .sort univ)
      | .const name lvls _ => do
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
            let value : Ipld.Both Ipld.Expr := ⟨ .const () constCid.anon $ univCids.map Ipld.Both.anon
                       , .const name constCid.meta $ univCids.map Ipld.Both.meta ⟩
            pure (value, .const name const univs)
      | .app fnc arg _ => do
        let (fncCid, fnc) ← toYatimaExpr fnc
        let (argCid, arg) ← toYatimaExpr arg
        let value : Ipld.Both Ipld.Expr := ⟨ .app fncCid.anon argCid.anon, .app fncCid.meta argCid.meta ⟩
        pure (value, .app fnc arg)
      | .lam name typ bod data =>
        let (typCid, typ) ← toYatimaExpr typ
        let (bodCid, bod) ← withName name $ toYatimaExpr bod
        let bnd := data.binderInfo
        let value : Ipld.Both Ipld.Expr := ⟨ .lam () bnd typCid.anon bodCid.anon, .lam name () typCid.meta bodCid.meta ⟩
        pure (value, .lam name bnd typ bod)
      | .forallE name dom img data =>
        let (domCid, dom) ← toYatimaExpr dom
        let (imgCid, img) ← withName name $ toYatimaExpr img
        let bnd := data.binderInfo
        let value : Ipld.Both Ipld.Expr := ⟨ .pi () bnd domCid.anon imgCid.anon, .pi name () domCid.meta imgCid.meta ⟩
        pure (value, .pi name bnd dom img)
      | .letE name typ exp bod _ =>
        let (typCid, typ) ← toYatimaExpr typ
        let (expCid, exp) ← toYatimaExpr exp
        let (bodCid, bod) ← withName name $ toYatimaExpr bod
        let value : Ipld.Both Ipld.Expr := ⟨ .letE () typCid.anon expCid.anon bodCid.anon, .letE name typCid.meta expCid.meta bodCid.meta ⟩
        pure (value, .letE name typ exp bod)
      | .lit lit _ =>
        let value : Ipld.Both Ipld.Expr := ⟨ .lit lit, .lit () ⟩
        pure (value, .lit lit)
      | .mdata _ e _ => unreachable!
      | .proj _ idx exp _ => do
        let (expCid, exp) ← toYatimaExpr exp
        let value : Ipld.Both Ipld.Expr := ⟨ .proj idx expCid.anon, .proj () expCid.meta ⟩
        pure (value, .proj idx exp)
      | .fvar .. => throw "Free variable found"
      | .mvar .. => throw "Metavariable found"
    let cid ← StoreValue.insert $ .expr value
    pure (cid, expr)

  partial def toYatimaInductive (initInd : Lean.InductiveVal) : CompileM (ConstCid × ConstIdx) := do
    -- `constList` is the list of the names of all constants associated with an inductive block: the inductives themselves,
    -- the constructors and the recursors.
    let mut constList : List Lean.Name := initInd.all
    for indName in initInd.all do
      match ← findConstant indName with
      | .inductInfo ind =>
        let leanRecs := (← read).constMap.childrenOfWith ind.name -- reverses once
          fun c => match c with | .recInfo _ => true | _ => false
        let leanRecs := leanRecs.map (·.name)
        constList := (constList.append ind.ctors).append leanRecs
      | const => throw s!"Invalid constant kind for '{const.name}'. Expected 'inductive' but got '{const.ctorName}'"

    -- All inductives, constructors and recursors are done in one go, so we must append an array of `constList.length` to `defns`
    -- and save the mapping of all names in `constList` to their respective indices
    let mut firstIdx ← modifyGet (fun stt => (stt.defns.size, { stt with defns := stt.defns.append (mkArray constList.length default) }))
    let mut mutualIdxs : RBMap Lean.Name (Nat × Nat) compare := RBMap.empty
    for (i, n) in constList.enum do
      mutualIdxs := mutualIdxs.insert n (i, firstIdx + i)

    -- This part will build the inductive block, but won't add the inductives, constructors and recursors to the cache
    let indInfos : Ipld.Both (List $ Ipld.Inductive ·) ← initInd.all.foldlM (init := ⟨[], []⟩) fun acc name => do
      match ← findConstant name with
      | .inductInfo ind => do
        withRecrs mutualIdxs do
          let ipldInd ← toYatimaIpldInductive ind
          pure ⟨ipldInd.anon :: acc.anon, ipldInd.meta :: acc.meta⟩
      | const => throw s!"Invalid constant kind for '{const.name}'. Expected 'inductive' but got '{const.ctorName}'"
    let indBlock := ⟨.mutIndBlock indInfos.anon, .mutIndBlock indInfos.meta⟩
    let indBlockCid ← StoreValue.insert $ .const indBlock

    let mut ret? : Option (ConstCid × ConstIdx) := none

    for (idx, name) in constList.enum do
      match ← findConstant name with
      | .inductInfo const =>
        let (typeCid, type) ← toYatimaExpr const.type
        let struct ← if const.isRec || const.numIndices != 0 then pure none else
          match const.ctors with
          | [ctor] => sorry
          | _ => pure none
        let unit := match struct with
          | some ctor => ctor.fields == 0
          | none => false
        let ind : Inductive := {
          name     := const.name
          lvls     := const.levelParams
          indices  := const.numIndices
          params   := const.numParams
          type     := type
          recr     := const.isRec
          refl     := const.isReflexive
          safe     := not const.isUnsafe
          unit     := unit
          struct   := struct}
        let indProj := ⟨.inductiveProj $ ind.toIpld idx typeCid indBlockCid, .inductiveProj $ ind.toIpld idx typeCid indBlockCid⟩
        let cid ← StoreValue.insert $ .const indProj
        let some (_, constIdx) := mutualIdxs.find? name | throw ""
        modify (fun stt => { stt with defns := stt.defns.set! constIdx (.inductive ind) })
        addToCache const.name (cid, constIdx)
        if name == initInd.name then ret? := some (cid, constIdx)
      | .ctorInfo const =>
        let ctorProj := ⟨.constructorProj sorry, .constructorProj sorry⟩
        let ctorProjCid ← StoreValue.insert $ .const ctorProj
        sorry
      | .recInfo const =>
        let recProj := ⟨.recursorProj sorry, .recursorProj sorry⟩
        let recProjCid ← StoreValue.insert $ .const recProj
        sorry
      | _ => unreachable!

    match ret? with
    | some ret => return ret
    | none => throw s!"Constant for '{initInd.name}' wasn't compiled"

  partial def toYatimaIpldInductive (ind : Lean.InductiveVal) :
      CompileM $ Ipld.Both Ipld.Inductive := do
    -- reverses once
    let leanRecs := (← read).constMap.childrenOfWith ind.name
      fun c => match c with | .recInfo _ => true | _ => false
    let (recs, ctors) : ((List $ Ipld.Both (Sigma $ Ipld.Recursor ·)) × (List $ Ipld.Both Ipld.Constructor)) :=
      -- reverses again, keeping original order
      ← leanRecs.foldlM (init := ([], [])) fun (recs, ctors) r =>
        match r with
        | .recInfo rv => do
          if ← isInternalRec rv.type ind.name then do
            let mut ctors := ctors
            let (thisRec, thisCtors) := ← toYatimaIpldInternalRec ind.ctors r
            let recs := (⟨Sigma.mk .Intr thisRec.anon, Sigma.mk .Intr thisRec.meta⟩) :: recs
            return (recs, ctors)
          else do
            let thisRec := ← toYatimaIpldExternalRec r
            --let rules ← rv.rules.mapM fun r => do 
            --  let (ctorCid, _) ← processYatimaConst $ ← findConstant r.ctor
            --  let (rhsCid, _) ← toYatimaExpr r.rhs
            --  return ⟨ctorCid.anon, r.nfields, rhsCid.anon⟩
            let recs := (⟨Sigma.mk .Extr thisRec.anon, Sigma.mk .Extr thisRec.meta⟩) :: recs
            return (recs, ctors)
        | _ => throw s!"Non-recursor {r.name} extracted from children"
    let (typeCid, type) ← toYatimaExpr ind.type
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

  partial def toYatimaIpldInternalRec (ctors : List Lean.Name) :
      Lean.ConstantInfo → CompileM (Ipld.Both (Ipld.Recursor · .Intr) × (List $ Ipld.Both Ipld.Constructor))
    | .recInfo rec => do
      withLevels rec.levelParams do
        let (typeCid, type) ← toYatimaExpr rec.type
        let ctorMap : RBMap Name Constructor compare := ← rec.rules.foldlM (init := (RBMap.empty)) fun ctorMap r => do
          match ctors.indexOf? r.ctor with
          | some _ =>
            let ctor ← toYatimaConstructor r
            return ctorMap.insert ctor.name ctor
          -- this is an external recursor rule
          | none => return ctorMap
        let retCtors ← ctors.mapM fun ctor => do
          match ctorMap.find? ctor with
          | some thisCtor => pure thisCtor
          | none => unreachable!
        return ({
          name    := rec.name
          lvls    := rec.levelParams
          type    := type
          params  := rec.numParams
          indices := rec.numIndices
          motives := rec.numMotives
          minors  := rec.numMinors
          k       := rec.k }, retCtors)
    | const => throw s!"Invalid constant kind for '{const.name}'. Expected 'recursor' but got '{const.ctorName}'"

  partial def toYatimaExternalRecRule (rule : Lean.RecursorRule) :
      CompileM RecursorRule := do
    let (rhsCid, rhs) ← toYatimaExpr rule.rhs
    let const ← findConstant rule.ctor
    let (ctorCid, ctor) ← processYatimaConst const
    match ← derefConst ctor with
    | .constructor ctor => return { ctor, fields := rule.nfields, rhs }
    | _ => throw s!"Invalid constant kind for '{const.name}'."

  partial def toYatimaIpldExternalRec :
      Lean.ConstantInfo → CompileM (Ipld.Both (Ipld.Recursor · .Extr))
    | .recInfo rec => do
      withLevels rec.levelParams do
        let (typeCid, type) ← toYatimaExpr rec.type
        let rules := ← rec.rules.foldlM (init := []) fun rules r => do
          let extRecrRule ← toYatimaExternalRecRule r
          return extRecrRule::rules
        return ⟨{
          name    := ()
          lvls    := rec.levelParams.length
          type    := type
          params  := rec.numParams
          indices := rec.numIndices
          motives := rec.numMotives
          minors  := rec.numMinors
          rules   := rules
          k       := rec.k },
          sorry⟩
    | const => throw s!"Invalid constant kind for '{const.name}'. Expected 'recursor' but got '{const.ctorName}'"
    
  partial def isInternalRec (expr : Lean.Expr) (name : Lean.Name) : CompileM Bool :=
    match expr with
      | .forallE _ t e _  => match e with
        | .forallE ..  => isInternalRec e name
        -- t is the major premise
        | _ => isInternalRec t name
      | .app e .. => isInternalRec e name
      | .const n .. => return n == name
      | _ => return false

  partial def toYatimaConstructor (rule : Lean.RecursorRule) : CompileM Constructor := do
      let (rhsCid, rhs) ← toYatimaExpr rule.rhs
      match ← findConstant rule.ctor with
        | .ctorInfo ctor =>
          let (typeCid, type) ← toYatimaExpr ctor.type
          return {
            rhs    := rhs
            idx    := ctor.cidx
            lvls   := ctor.levelParams
            name   := ctor.name
            type   := type
            safe   := not ctor.isUnsafe
            params := ctor.numParams
            fields := ctor.numFields }
        | const => throw s!"Invalid constant kind for '{const.name}'. Expected 'constructor' but got '{const.ctorName}'"

  partial def toYatimaDef (struct : Lean.DefinitionVal) : CompileM (ConstCid × ConstIdx) := do
    if struct.all.length == 1 then
      let constIdx ← modifyGet (fun stt => (stt.defns.size, { stt with defns := stt.defns.push default }))
      let (value, defn) ← withRecrs (RBMap.single struct.name (0, constIdx)) $ toYatimaDefIpld struct
      let cid ← StoreValue.insert $ .const ⟨ .definition value.anon, .definition value.meta ⟩
      modify (fun stt => { stt with defns := stt.defns.set! constIdx (.definition defn) })
      addToCache struct.name (cid, constIdx)
      pure (cid, constIdx)
    else
      let mutualDefs ← struct.all.mapM fun name => do
        match ← findConstant name with
        | .defnInfo defn => pure defn
        | _ => throw s!"Unknown definition '{name}'"
      let mutualDefs ← sortDefs [mutualDefs]
      let mutualSize := struct.all.length
      let mut firstIdx ← modifyGet (fun stt => (stt.defns.size, { stt with defns := stt.defns.append (mkArray mutualSize default) }))
      let mut mutualIdxs : RBMap Lean.Name (Nat × Nat) compare := RBMap.empty
      for (i, ds) in mutualDefs.enum do
        for d in ds do
          -- TODO Isn't `mutDefIdx` unnecessary? Couldn't we use `mutualIdxs` instead?
          modify (fun stt => { stt with mutDefIdx := stt.mutDefIdx.insert d.name i })
          mutualIdxs := mutualIdxs.insert d.name (i, firstIdx + i)
      let definitions ← withRecrs mutualIdxs $
        mutualDefs.mapM fun ds => ds.mapM $ toYatimaDefIpld
      let definitionsAnon := (definitions.map fun ds => match ds.head? with | some d => [Ipld.Both.anon d.1] | none => []).join
      let definitionsMeta := definitions.map fun ds => ds.map $ Ipld.Both.meta ∘ Prod.fst
      let block : Ipld.Both Ipld.Const := ⟨ .mutDefBlock definitionsAnon, .mutDefBlock definitionsMeta ⟩
      let blockCid ← StoreValue.insert $ .const block

      let mut ret? : Option (ConstCid × ConstIdx) := none

      for (⟨defnAnon, defnMeta⟩, defn) in definitions.join do
        let idx : Nat := match (← get).mutDefIdx.find? defn.name with
          | some i => i
          | none => unreachable!
        let value := ⟨ .definitionProj $ ⟨(), defn.lvls.length, defnAnon.type, blockCid.anon, idx⟩
                     , .definitionProj $ ⟨defn.name, defn.lvls, defnMeta.type, blockCid.meta, ()⟩ ⟩
        let cid ← StoreValue.insert $ .const value
        let constIdx := idx + firstIdx
        modify (fun stt => { stt with defns := stt.defns.set! constIdx (.definition defn) })
        addToCache struct.name (cid, constIdx)
        if defn.name == struct.name.toString then ret? := some (cid, constIdx)

      match ret? with
      | some ret => return ret
      | none => throw s!"Constant for '{struct.name}' wasn't compiled"

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
    | .mvar .., _ => throw "Unfilled expr metavariable"
    | _, .mvar .. => throw "Unfilled expr metavariable"
    | .fvar .., _ => throw "expr free variable"
    | _, .fvar .. => throw "expr free variable"
    | .mdata _ x _, .mdata _ y _  => cmpExpr names x y
    | .mdata _ x _, y  => cmpExpr names x y
    | x, .mdata _ y _  => cmpExpr names x y
    | .bvar x _, .bvar y _ => return (compare x y)
    | .bvar _ _, _ => return .lt
    | _, .bvar _ _ => return .gt
    | .sort x _, .sort y _ => cmpLevel x y
    | .sort _ _, _ => return .lt
    | _, .sort _ _ => return .gt
    | .const x xls _, .const y yls _ => do
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
    | .const _ _ _, _ => return .lt
    | _, .const _ _ _ => return .gt
    | .app xf xa _, .app yf ya _ => (· * ·) <$> cmpExpr names xf yf <*> cmpExpr names xa ya
    | .app _ _ _, _ => return .lt
    | _, .app _ _ _ => return .gt
    | .lam _ xt xb _, .lam _ yt yb _ => (· * ·) <$> cmpExpr names xt yt <*> cmpExpr names xb yb
    | .lam _ _ _ _, _ => return .lt
    | _, .lam _ _ _ _ => return .gt
    | .forallE _ xt xb _, .forallE _ yt yb _ => (· * ·) <$> cmpExpr names xt yt <*> cmpExpr names xb yb
    | .forallE _ _ _ _, _ => return .lt
    | _, .forallE _ _ _ _ => return .gt
    | .letE _ xt xv xb _, .letE _ yt yv yb _ => (· * · * ·) <$> cmpExpr names xt yt <*> cmpExpr names xv yv <*> cmpExpr names xb yb
    | .letE _ _ _ _ _, _ => return .lt
    | _, .letE _ _ _ _ _ => return .gt
    | .lit x _, .lit y _ =>
      return if x < y then .lt else if x == y then .eq else .gt
    | .lit _ _, _ => return .lt
    | _, .lit _ _ => return .gt
    | .proj _ nx tx _, .proj _ ny ty _ => do
      let ts ← cmpExpr names tx ty
      return concatOrds [ compare nx ny , ts ]

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
    let normDss := dss.map fun ds => List.sort $ ds.map (·.name)
    let normNewDss := newDss.map fun ds => List.sort $ ds.map (·.name)
    if normDss == normNewDss then
      return newDss
    else
      sortDefs newDss

end

open PrintLean PrintYatima in
def buildStore (constMap : Lean.ConstMap) (log : Bool) : CompileM Unit := do
  constMap.forM fun name const => do
    if log then
      dbg_trace "\n========================================="
      dbg_trace s!"Processing: {name}"
      dbg_trace "========================================="
    if log then
      dbg_trace "------------- Lean constant -------------"
      dbg_trace s!"{printLeanConst const}"
    let (_, const) ← processYatimaConst const
    if log then
      dbg_trace "------------ Yatima constant ------------"
      dbg_trace s!"{← printYatimaConst true (← derefConst const)}"
  return ()

def extractEnv (map map₀ : Lean.ConstMap) (log : Bool) (stt : CompileState) :
    Except String CompileState :=
  let map  := Lean.filterConstants map
  let map₀ := Lean.filterConstants map₀
  let delta : Lean.ConstMap := map.fold
    (init := Lean.SMap.empty) fun acc n c =>
      match map₀.find? n with
      | some c' => if c == c' then acc else acc.insert n c
      | none    => acc.insert n c
  CompileM.run ⟨map, [], [], .empty⟩ stt (buildStore delta log)

def getPaths : IO Lean.SearchPath := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["print-paths"]
  }
  let split := out.stdout.splitOn "\"oleanPath\":[" |>.getD 1 ""
  let split := split.splitOn "],\"loadDynlibPaths\":[" |>.getD 0 ""
  return split.replace "\"" "" |>.splitOn ","|>.map fun s => ⟨s⟩

def runFrontend (filePath : System.FilePath)
  (log : Bool := false) (stt : CompileState := default) :
    IO $ Except String CompileState := do
  Lean.initSearchPath (← Lean.findSysroot) (← getPaths)
  let (env, ok) ← Lean.Elab.runFrontend (← IO.FS.readFile filePath) .empty
    filePath.toString default
  if ok then
    let importFile := env.header.imports.map (·.module) |>.foldl
      (init := "prelude\n")
      fun acc m => s!"{acc}import {m}\n"
    let (env₀, _) ← Lean.Elab.runFrontend importFile .empty default default
    match extractEnv env.constants env₀.constants log stt with
    | .ok  stt => return .ok stt
    | .error e => return .error e
  else
    return .error s!"Lean frontend failed on file {filePath}"

end Yatima.Compiler
