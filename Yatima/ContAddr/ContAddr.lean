import Yatima.ContAddr.Printing
import Yatima.Ipld.ToIpld
import YatimaStdLib.RBMap
import Yatima.Ipld.PrimCids

/-- Move to YatimaStdLib -/
instance : HMul Ordering Ordering Ordering where hMul
  | .gt, _ => .gt
  | .lt, _ => .lt
  | .eq, x => x

/-- Move to YatimaStdLib -/
def concatOrds : List Ordering → Ordering :=
  List.foldl (fun x y => x * y) .eq

namespace Yatima.ContAddr

open Std (RBMap)

open Ipld

/-- Gets a constant from the array of constants -/
def derefConst (idx : TC.ConstIdx) : ContAddrM TC.Const := do
  let consts := (← get).tcStore.consts
  let size := consts.size
  if h : idx < size then
    return consts[idx]'h
  else
    throw $ .invalidConstantIndex idx size

/-- Retrieves a Lean constant from the environment by its name -/
def getLeanConstant (name : Lean.Name) : ContAddrM Lean.ConstantInfo := do
  match (← read).constMap.find? name with
  | some const => pure const
  | none => throw $ .unknownConstant name

/-- Content-addresses a Lean universe level and adds it to the store -/
def contAddrUniv (l : Lean.Level) : ContAddrM (IR.BothUnivCid × TC.Univ) := do
  let (value, univ) ← match l with
    | .zero =>
      let value := ⟨ .zero, .zero ⟩
      pure (value, .zero)
    | .succ n    =>
      let (univCid, univ) ← contAddrUniv n
      let value := ⟨ .succ univCid.anon, .succ univCid.meta ⟩
      pure (value, .succ univ)
    | .max  a b  =>
      let (univACid, univA) ← contAddrUniv a
      let (univBCid, univB) ← contAddrUniv b
      let value := ⟨ .max univACid.anon univBCid.anon,
        .max univACid.meta univBCid.meta ⟩
      pure (value, .max univA univB)
    | .imax  a b  =>
      let (univACid, univA) ← contAddrUniv a
      let (univBCid, univB) ← contAddrUniv b
      let value := ⟨ .imax univACid.anon univBCid.anon,
        .imax univACid.meta univBCid.meta ⟩
      pure (value, .imax univA univB)
    | .param name =>
      let lvls := (← read).univCtx
      match lvls.indexOf? name with
      | some n =>
        let value := ⟨ .var n, .var name ⟩
        pure (value, .var name n)
      | none   => throw $ .levelNotFound name lvls
    | .mvar .. => throw $ .unfilledLevelMetavariable l
  let cid ← addToStore $ .univ value
  pure (cid, univ)

/-- Defines an ordering for Lean universes -/
def cmpLevel (x : Lean.Level) (y : Lean.Level) : ContAddrM Ordering :=
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

def isInternalRec (expr : Lean.Expr) (name : Lean.Name) : Bool :=
  match expr with
  | .forallE _ t e _  => match e with
    | .forallE ..  => isInternalRec e name
    -- t is the major premise
    | _ => isInternalRec t name
  | .app e .. => isInternalRec e name
  | .const n .. => n == name
  | _ => false

mutual
  /--
  Gets the Yatima constant references off of a Lean constant, returning its CID
  and its index in the array of constants.

  If the result is already cached, returns it right away. Otherwise, calls
  `contAddrConstant` to do the actual content-addressing.
  -/
  partial def getContAddrConst (const : Lean.ConstantInfo) :
      ContAddrM $ IR.BothConstCid × TC.ConstIdx := do
    let name := const.name
    let log  := (← read).log
    match (← get).cache.find? name with
    | some c => pure c
    | none   =>
      if log then
        IO.println s!"↡ Stacking {name}{const.formatAll}"
      let c ← contAddrConstant const
      if log then
        IO.println s!"↟ Popping  {name}"
      return c

  /--
  Consent-addresses Lean constants.

  For the `.defnInfo`, `.inductInfo`, `.ctorInfo` and `.recInfo`  cases, the
  side-effects are responsability of the auxiliary functions.

  For other cases, adds them to the cache, the store and the array of constants.
  -/
  partial def contAddrConstant : Lean.ConstantInfo → ContAddrM (IR.BothConstCid × TC.ConstIdx)
  -- These cases add multiple constants at the same time
  | .defnInfo struct => withLevelsAndReset struct.levelParams $ contAddrDefinition struct
  | .inductInfo struct => withLevelsAndReset struct.levelParams $ contAddrInductive struct
  -- These cases are subsumed by the inductive case
  | .ctorInfo struct => do
    discard $ match ← getLeanConstant struct.induct with
      | .inductInfo ind => getContAddrConst (.inductInfo ind)
      | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
    getContAddrConst (.ctorInfo struct)
  | .recInfo struct => do
    discard $ match ← getLeanConstant struct.getInduct with
      | .inductInfo ind => getContAddrConst (.inductInfo ind)
      | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
    getContAddrConst (.recInfo struct)
  -- The rest adds the constants to the cache one by one
  | const => withLevelsAndReset const.levelParams do
    -- It is important to push first with some value so we don't lose the
    -- position of the constant in a recursive call
    let constIdx ← modifyGet fun stt =>
      (stt.tcStore.consts.size,
        { stt with tcStore := { stt.tcStore with consts := stt.tcStore.consts.push default } })
    let values : IR.Both IR.Const × Const ← match const with
      | .axiomInfo struct =>
        let (typeCid, type) ← contAddrExpr struct.type
        let ax := {
          name := struct.name
          lvls := struct.levelParams
          type := type
          safe := not struct.isUnsafe }
        let value := ⟨ .axiom $ ax.toIR typeCid, .axiom $ ax.toIR typeCid ⟩
        pure (value, .axiom ax)
      | .thmInfo struct =>
        let (typeCid, type) ← contAddrExpr struct.type
        -- Theorems are never truly recursive, though they can use recursive schemes
        let (valueCid, value) ← contAddrExpr struct.value
        let thm := {
          name  := struct.name
          lvls  := struct.levelParams
          type  := type
          value := value }
        let value := ⟨.theorem $ thm.toIR typeCid valueCid, .theorem $ thm.toIR typeCid valueCid⟩
        pure (value, .theorem thm)
      | .opaqueInfo struct =>
        let (typeCid, type) ← contAddrExpr struct.type
        let (valueCid, value) ← withRecrs (RBMap.single struct.name (0, some 0, constIdx)) $ contAddrExpr struct.value
        let opaq := {
          name  := struct.name
          lvls  := struct.levelParams
          type  := type
          value := value
          safe  := not struct.isUnsafe }
          let value := ⟨ .opaque $ opaq.toIR typeCid valueCid, .opaque $ opaq.toIR typeCid valueCid ⟩
        pure (value, .opaque opaq)
      | .quotInfo struct =>
        let (typeCid, type) ← contAddrExpr struct.type
        let quot := {
          name := struct.name
          lvls := struct.levelParams
          type := type
          kind := struct.kind }
        let value := ⟨ .quotient $ quot.toIR typeCid, .quotient $ quot.toIR typeCid ⟩
        pure (value, .quotient quot)
      | _ => unreachable! -- the other cases were already dealt with
    let cid ← addToStore $ .const values.fst
    addToConsts constIdx values.snd
    addToCache const.name (cid, constIdx)
    pure (cid, constIdx)

  /--
  Content-addresses a Lean expression and adds it to the store.

  Constants are the tricky case, for which there are two possibilities:
  * The constant belongs to `recrCtx`, representing a recursive call. Those are
  encoded as variables with indexes that go beyond the bind indexes
  * The constant doesn't belong to `recrCtx`, meaning that it's not a recursion
  and thus we can contAddr the actual constant right away
  -/
  partial def contAddrExpr : Lean.Expr → ContAddrM (IR.BothExprCid × TC.Expr)
  | .mdata _ e => contAddrExpr e
  | expr => do
    match expr with
      | .bvar idx => match (← read).bindCtx.get? idx with
        -- Bound variables must be in the bind context
        | some name =>
          let value := ⟨ .var idx () [], .var name (.injᵣ none) [] ⟩
          let cid ← addToStore $ .expr value
          pure (cid, .var name idx)
        | none => throw $ .invalidBVarIndex idx
      | .sort lvl =>
        let (univCid, univ) ← contAddrUniv lvl
        let value := ⟨ .sort univCid.anon, .sort univCid.meta ⟩
        let cid ← addToStore $ .expr value
        pure (cid, .sort univ)
      | .const name lvls =>
        let pairs ← lvls.mapM $ contAddrUniv
        let (univCids, univs) ← pairs.foldrM (init := ([], []))
          fun pair pairs => pure (pair.fst :: pairs.fst, pair.snd :: pairs.snd)
        match (← read).recrCtx.find? name with
        | some (i, i?, ref) => -- recursing!
          let idx := (← read).bindCtx.length + i
          let value := ⟨ .var idx () (univCids.map (·.anon)),
            .var name i? (univCids.map (·.meta)) ⟩
          let cid ← addToStore $ .expr value
          pure (cid, .const name ref univs)
        | none =>
          let const ← getLeanConstant name
          let (constCid, const) ← getContAddrConst const
          let value := ⟨ .const () constCid.anon $ univCids.map (·.anon),
            .const name constCid.meta $ univCids.map (·.meta) ⟩
          let cid ← addToStore $ .expr value
          pure (cid, .const name const univs)
      | .app fnc arg =>
        let (fncCid, fnc) ← contAddrExpr fnc
        let (argCid, arg) ← contAddrExpr arg
        let value := ⟨ .app fncCid.anon argCid.anon, .app fncCid.meta argCid.meta ⟩
        let cid ← addToStore $ .expr value
        pure (cid, .app fnc arg)
      | .lam name typ bod bnd =>
        let (typCid, typ) ← contAddrExpr typ
        let (bodCid, bod) ← withBinder name $ contAddrExpr bod
        let value := ⟨ .lam () bnd typCid.anon bodCid.anon,
          .lam name () typCid.meta bodCid.meta ⟩
        let cid ← addToStore $ .expr value
        pure (cid, .lam name bnd typ bod)
      | .forallE name dom img bnd =>
        let (domCid, dom) ← contAddrExpr dom
        let (imgCid, img) ← withBinder name $ contAddrExpr img
        let value := ⟨ .pi () bnd domCid.anon imgCid.anon,
          .pi name () domCid.meta imgCid.meta ⟩
        let cid ← addToStore $ .expr value
        pure (cid, .pi name bnd dom img)
      | .letE name typ exp bod _ =>
        let (typCid, typ) ← contAddrExpr typ
        let (expCid, exp) ← contAddrExpr exp
        let (bodCid, bod) ← withBinder name $ contAddrExpr bod
        let value := ⟨ .letE () typCid.anon expCid.anon bodCid.anon,
          .letE name typCid.meta expCid.meta bodCid.meta ⟩
        let cid ← addToStore $ .expr value
        pure (cid, .letE name typ exp bod)
      | .lit lit =>
        let value := ⟨ .lit lit, .lit () ⟩
        let cid ← addToStore $ .expr value
        pure (cid, .lit lit)
      | .proj _ idx exp =>
        let (expCid, exp) ← contAddrExpr exp
        let value := ⟨ .proj idx expCid.anon, .proj () expCid.meta ⟩
        let cid ← addToStore $ .expr value
        pure (cid, .proj idx exp)
      | .fvar ..  => throw $ .freeVariableExpr expr
      | .mvar ..  => throw $ .metaVariableExpr expr
      | .mdata .. => throw $ .metaDataExpr expr

  /--
  Content-addresses an inductive and all inductives in the mutual block as a
  mutual block, even if the inductive itself is not in a mutual block.

  Content-addressing an inductive involves content-addressing its associated
  constructors and recursors, hence the lenght of this function.
  -/
  partial def contAddrInductive (initInd : Lean.InductiveVal) :
      ContAddrM (IR.BothConstCid × TC.ConstIdx) := do
    let mut inds := []
    let mut indCtors := []
    let mut indRecs := []

    for indName in initInd.all do
      match ← getLeanConstant indName with
      | .inductInfo ind =>
        let leanRecs := ((← read).constMap.childrenOfWith ind.name
          fun c => match c with | .recInfo _ => true | _ => false).map (·.name)
        inds := inds ++ [indName]
        indCtors := indCtors ++ ind.ctors
        indRecs := indRecs ++ leanRecs
      | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName

    let mut firstIdx : TC.ConstIdx := (← get).tcStore.consts.size

    -- `mutualConsts` is the list of the names of all constants associated with an
    -- inductive block: the inductives themselves, the constructors and the recursors
    let mutualConsts := inds ++ indCtors ++ indRecs
    let all := mutualConsts.enum.map (firstIdx + ·.1)

    -- All inductives, constructors and recursors are done in one go, so we must
    -- append an array of `mutualConsts.length` to `consts` and save the mapping
    -- of all names in `mutualConsts` to their respective indices
    modify fun stt => { stt with tcStore := { stt.tcStore with
      consts := stt.tcStore.consts ++ mkArray mutualConsts.length default } }

    let recrCtx := mutualConsts.enum.foldl (init := default)
      fun acc (i, n) => acc.insert n (i, none, firstIdx + i)

    -- This part will build the inductive block and add all inductives,
    -- constructors and recursors to `consts`
    let irInds : List (IR.Both IR.Inductive) ← initInd.all.foldrM (init := [])
      fun name acc => do
        match ← getLeanConstant name with
        | .inductInfo ind =>
          withRecrs recrCtx do
            pure $ (← inductiveToIR ind all) :: acc
        | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
    let indBlockCid ← addToStore $ .const
      ⟨.mutIndBlock $ irInds.map (·.anon), .mutIndBlock $ irInds.map (·.meta)⟩

    -- While iterating on the inductives from the mutual block, we need to track
    -- the correct objects to return
    let mut ret? : Option (IR.BothConstCid × TC.ConstIdx) := none

    -- `constIdx` keeps track of the constant index for the next addition to cache
    let mut constIdx := firstIdx

    for (indIdx, ⟨indAnon, indMeta⟩) in irInds.enum do
      -- Store and cache inductive projections
      let name := indMeta.name.projᵣ
      let indProj :=
        ⟨ .inductiveProj ⟨ (), indAnon.lvls, indAnon.type, indBlockCid.anon, indIdx ⟩
        , .inductiveProj ⟨ indMeta.name, indMeta.lvls, indMeta.type, indBlockCid.meta, () ⟩ ⟩
      let cid ← addToStore $ .const indProj
      if name == initInd.name then ret? := some (cid, constIdx)
      addToCache name (cid, constIdx)
      constIdx := constIdx + 1

    for (indIdx, ⟨indAnon, indMeta⟩) in irInds.enum do
      for (ctorIdx, (ctorAnon, ctorMeta)) in (indAnon.ctors.zip indMeta.ctors).enum do
        -- Store and cache constructor projections
        let name := ctorMeta.name.projᵣ
        let ctorProj :=
          ⟨ .constructorProj ⟨ (), ctorAnon.lvls, ctorAnon.type, indBlockCid.anon, indIdx, ctorIdx ⟩
          , .constructorProj ⟨ ctorMeta.name, ctorMeta.lvls, ctorMeta.type, indBlockCid.meta, (), () ⟩ ⟩
        let cid ← addToStore $ .const ctorProj
        addToCache name (cid, constIdx)
        constIdx := constIdx + 1

    for (indIdx, ⟨indAnon, indMeta⟩) in irInds.enum do
      for (recrIdx, (recrAnon, recrMeta)) in (indAnon.recrs.zip indMeta.recrs).enum do
        -- Store and cache recursor projections
        let name := recrMeta.name.projᵣ
        let recrProj :=
          ⟨ .recursorProj ⟨ (), recrAnon.lvls, recrAnon.type, indBlockCid.anon, indIdx, recrIdx ⟩
          , .recursorProj ⟨ recrMeta.name, recrMeta.lvls, recrMeta.type, indBlockCid.meta, (), () ⟩ ⟩
        let cid ← addToStore $ .const recrProj
        addToCache name (cid, constIdx)
        constIdx := constIdx + 1

    match ret? with
    | some ret => return ret
    | none => throw $ .constantNotContentAddressed initInd.name

  /-- Encodes a Lean inductive to IR -/
  partial def inductiveToIR (ind : Lean.InductiveVal) (all : List TC.ConstIdx) :
      ContAddrM $ IR.Both IR.Inductive := do
    let (_, _, indIdx) ← getFromRecrCtx! ind.name
    let leanRecs := (← read).constMap.childrenOfWith ind.name
      fun c => match c with | .recInfo _ => true | _ => false
    let (recs, ctors) : (List $ IR.Both IR.Recursor) ×
        (List $ IR.Both IR.Constructor) :=
      ← leanRecs.foldrM (init := ([], [])) fun r (recs, ctors) => do
        match r with
        | .recInfo rv =>
          if isInternalRec rv.type ind.name then
            let (thisRec, thisCtors) := ← internalRecToIR ind.ctors indIdx all r
            let recs := ⟨thisRec.anon, thisRec.meta⟩ :: recs
            return (recs, thisCtors)
          else
            let thisRec ← externalRecToIR indIdx all r
            let recs := ⟨thisRec.anon, thisRec.meta⟩ :: recs
            return (recs, ctors)
        | _ => throw $ .nonRecursorExtractedFromChildren r.name
    let (typeCid, type) ← contAddrExpr ind.type
    -- Structures can't be recursive nor have indices
    let struct ← if ind.isRec || ind.numIndices != 0 then pure none else
      match ind.ctors with
      -- Structures can only have one constructor
      | [ctorName] => do
        let (_, _, ctorIdx) ← getFromRecrCtx! ctorName
        pure $ some ctorIdx
      | _ => pure none
    let unit ← match struct with
      | some ctorIdx =>
        match ← derefConst ctorIdx with
        | .constructor ctor => pure $ ctor.fields == 0
        | const => throw $ .invalidConstantKind const.name "constructor" const.ctorName
      | none => pure false
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
    addToConsts indIdx tcInd
    return {
      anon := ⟨ ()
        , ind.levelParams.length
        , typeCid.anon
        , ind.numParams
        , ind.numIndices
        -- NOTE: for the purpose of extraction, the order of `ctors` and `recs`
        -- MUST match the order used in `recrCtx`
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

  /-- Encodes an internal recursor to IR -/
  partial def internalRecToIR (ctors : List Lean.Name) (ind : TC.ConstIdx) (all : List TC.ConstIdx) : Lean.ConstantInfo → ContAddrM ((IR.Both IR.Recursor) × (List $ IR.Both IR.Constructor))
    | .recInfo rec => do
      withLevels rec.levelParams do
        let (typeCid, type) ← contAddrExpr rec.type
        let (retCtors, retRules, tcRules) ← rec.rules.foldrM (init := ([], [], [])) fun r acc@(retCtors, retRules, tcRules) => do
          if ctors.contains r.ctor then
            let (ctor, rule, tcRule) ← recRuleToIR r
            pure $ (ctor :: retCtors, rule :: retRules, tcRule :: tcRules)
          -- this is an external recursor rule
          else pure acc
        let tcRecr := .recursor {
          name     := rec.name
          lvls     := rec.levelParams
          type     := type
          params   := rec.numParams
          indices  := rec.numIndices
          motives  := rec.numMotives
          minors   := rec.numMinors
          rules    := tcRules
          isK      := rec.k
          ind      := ind
          all      := all
          internal := true }
        let (_, _, constIdx) ← getFromRecrCtx! rec.name
        addToConsts constIdx tcRecr
        let recr := ⟨
          { name    := ()
            lvls    := rec.levelParams.length
            type    := typeCid.anon
            params  := rec.numParams
            indices := rec.numIndices
            motives := rec.numMotives
            minors  := rec.numMinors
            rules   := retRules.map (·.anon)
            isK     := rec.k
            internal:= true
          },
          { name    := rec.name
            lvls    := rec.levelParams
            type    := typeCid.meta
            params  := ()
            indices := ()
            motives := ()
            minors  := ()
            rules   := retRules.map (·.meta)
            isK     := ()
            internal:= ()
            } ⟩
        return (recr, retCtors)
    | const => throw $ .invalidConstantKind const.name "recursor" const.ctorName

  /-- Encodes a Lean constructor to IR -/
  partial def recRuleToIR (rule : Lean.RecursorRule) :
      ContAddrM ((IR.Both IR.Constructor) × (IR.Both IR.RecursorRule) × TC.RecursorRule) := do
    let (rhsCid, rhs) ← contAddrExpr rule.rhs
    match ← getLeanConstant rule.ctor with
    | .ctorInfo ctor =>
      withLevels ctor.levelParams do
      let (typeCid, type) ← contAddrExpr ctor.type
      let tcCtor := {
        name    := ctor.name
        lvls    := ctor.levelParams
        type    := type
        idx     := ctor.cidx
        params  := ctor.numParams
        fields  := ctor.numFields
        safe    := not ctor.isUnsafe
      }
      let (_, _, constIdx) ← getFromRecrCtx! ctor.name
      addToConsts constIdx (.constructor tcCtor)
      let tcRule := {
        fields := rule.nfields
        rhs    := rhs
      }
      let ctor : IR.Both IR.Constructor := ⟨
        { lvls   := ctor.levelParams.length
          name   := ()
          type   := typeCid.anon
          idx    := ctor.cidx
          params := ctor.numParams
          fields := ctor.numFields
          safe   := not ctor.isUnsafe },
        { lvls   := ctor.levelParams
          name   := ctor.name
          type   := typeCid.meta
          idx    := ()
          params := ()
          fields := ()
          safe   := () } ⟩
      let rule := ⟨
        { fields := rule.nfields
          rhs    := rhsCid.anon },
        { fields := ()
          rhs    := rhsCid.meta } ⟩
      pure (ctor, rule, tcRule)
    | const => throw $ .invalidConstantKind const.name "constructor" const.ctorName

  /-- Encodes an external recursor to IR -/
  partial def externalRecToIR  (ind : TC.ConstIdx) (all : List TC.ConstIdx) : Lean.ConstantInfo → ContAddrM (IR.Both IR.Recursor)
    | .recInfo rec =>
      withLevels rec.levelParams do
        let (typeCid, type) ← contAddrExpr rec.type
        let (rules, tcRules) : IR.Both (fun k => List $ IR.RecursorRule k) × List TC.RecursorRule := ← rec.rules.foldrM
          (init := (⟨[], []⟩, [])) fun r rules => do
            let (recrRule, tcRecrRule) ← extRecRuleToIR r
            return (⟨recrRule.anon::rules.1.anon, recrRule.meta::rules.1.meta⟩, tcRecrRule::rules.2)
        let tcRecr := .recursor {
          name     := rec.name
          lvls     := rec.levelParams
          type     := type
          params   := rec.numParams
          indices  := rec.numIndices
          motives  := rec.numMotives
          minors   := rec.numMinors
          rules    := tcRules
          isK      := rec.k
          ind      := ind
          all      := all
          internal := false }
        let (_, _, constIdx) ← getFromRecrCtx! rec.name
        addToConsts constIdx tcRecr
        return ⟨
          { name    := ()
            lvls    := rec.levelParams.length
            type    := typeCid.anon
            params  := rec.numParams
            indices := rec.numIndices
            motives := rec.numMotives
            minors  := rec.numMinors
            rules   := rules.anon
            internal:= false
            isK     := rec.k },
          { name    := rec.name
            lvls    := rec.levelParams
            type    := typeCid.meta
            params  := ()
            indices := ()
            motives := ()
            minors  := ()
            rules   := rules.meta
            internal:= ()
            isK     := () } ⟩
    | const => throw $ .invalidConstantKind const.name "recursor" const.ctorName

  /-- Encodes a recursor rule to IPLD -/
  partial def extRecRuleToIR (rule : Lean.RecursorRule) :
      ContAddrM (IR.Both IR.RecursorRule × TC.RecursorRule) := do
    let (rhsCid, rhs) ← contAddrExpr rule.rhs
    let recrRule := ⟨
      { fields := rule.nfields, rhs := rhsCid.anon },
      { fields := (), rhs := rhsCid.meta }⟩
    let tcRecrRule := { fields := rule.nfields, rhs := rhs }
    return (recrRule, tcRecrRule)

  /--
  Content-addresses adefinition and all definitions in the mutual block as a mutual
  block, even if the definition itself is not in a mutual block.

  This function is rather similar to `Yatima.ContAddr.contAddrInductive`.
  -/
  partial def contAddrDefinition (struct : Lean.DefinitionVal) :
      ContAddrM (IR.BothConstCid × TC.ConstIdx) := do
    let mutualSize := struct.all.length

    -- This solves an issue in which the constant name comes different in the
    -- `all` attribute
    let all := if mutualSize == 1 then [struct.name] else struct.all

    -- Collecting and sorting all definitions in the mutual block
    let mutualDefs ← all.mapM fun name => do
      match ← getLeanConstant name with
      | .defnInfo defn => pure defn
      | const => throw $ .invalidConstantKind const.name "definition" const.ctorName
    let mutualDefs ← sortDefs [mutualDefs]

    -- Reserving the slots in the array of constants
    let mut firstIdx ← modifyGet fun stt =>
      (stt.tcStore.consts.size,
        { stt with tcStore := { stt.tcStore with
          consts := stt.tcStore.consts ++ mkArray mutualSize default } })

    -- Building the `recrCtx`
    let mut recrCtx := RBMap.empty
    let mut mutIdx := 0
    for (i, ds) in mutualDefs.enum do
      for (j, d) in ds.enum do
        recrCtx := recrCtx.insert d.name (i, some j, firstIdx + mutIdx)
        mutIdx := mutIdx + 1

    let all := recrCtx.toList.map fun (_, _, _, x) => x
    let definitions ← withRecrs recrCtx $ mutualDefs.mapM (·.mapM (definitionToIR all))

    -- Building and storing the block
    let definitionsAnon := (definitions.map fun ds => match ds.head? with | some d => [d.1.anon] | none => []).join
    let definitionsMeta := definitions.map fun ds => ds.map $ (·.meta) ∘ Prod.fst
    let block : IR.Both IR.Const := ⟨ .mutDefBlock definitionsAnon, .mutDefBlock definitionsMeta ⟩
    let blockCid ← addToStore $ .const block

    -- While iterating on the definitions from the mutual block, we need to track
    -- the correct objects to return
    let mut ret? : Option (IR.BothConstCid × TC.ConstIdx) := none

    let mut i : Nat := 0
    for (⟨defnAnon, defnMeta⟩, defn) in definitions.join do
      -- Storing and caching the definition projection
      -- Also adds the constant to the array of constants
      let some (idx, _) := recrCtx.find? defn.name | throw $ .cantFindMutDefIndex defn.name
      let value := ⟨ .definitionProj $ ⟨(), defn.lvls.length, defnAnon.type, blockCid.anon, idx⟩
                   , .definitionProj $ ⟨defn.name, defn.lvls, defnMeta.type, blockCid.meta, i⟩ ⟩
      let cid ← addToStore $ .const value
      let constIdx := i + firstIdx
      addToCache defn.name (cid, constIdx)
      addToConsts constIdx $ .definition defn
      if defn.name == struct.name then ret? := some (cid, constIdx)
      i := i + 1

    match ret? with
    | some ret => return ret
    | none => throw $ .constantNotContentAddressed struct.name

  /-- Encodes a definition to IR -/
  partial def definitionToIR
    (all : List TC.ConstIdx) (defn : Lean.DefinitionVal) :
      ContAddrM (IR.Both IR.Definition × TC.Definition) := do
    let (typeCid, type) ← contAddrExpr defn.type
    let (valueCid, value) ← contAddrExpr defn.value
    let defn := {
      name   := defn.name
      lvls   := defn.levelParams
      type
      value
      safety := defn.safety
      all    := all.sort }
    return (⟨defn.toIR typeCid valueCid, defn.toIR typeCid valueCid⟩, defn)

  /--
  A name-irrelevant ordering of Lean expressions.
  `weakOrd` contains the best known current mutual ordering
  -/
  partial def cmpExpr (weakOrd : Std.RBMap Name Nat compare) :
      Lean.Expr → Lean.Expr → ContAddrM Ordering
    | e@(.mvar ..), _ => throw $ .unfilledExprMetavariable e
    | _, e@(.mvar ..) => throw $ .unfilledExprMetavariable e
    | e@(.fvar ..), _ => throw $ .freeVariableExpr e
    | _, e@(.fvar ..) => throw $ .freeVariableExpr e
    | .mdata _ x, .mdata _ y  => cmpExpr weakOrd x y
    | .mdata _ x, y  => cmpExpr weakOrd x y
    | x, .mdata _ y  => cmpExpr weakOrd x y
    | .bvar x, .bvar y => return (compare x y)
    | .bvar .., _ => return .lt
    | _, .bvar .. => return .gt
    | .sort x, .sort y => cmpLevel x y
    | .sort .., _ => return .lt
    | _, .sort .. => return .gt
    | .const x xls, .const y yls => do
      let univs ← concatOrds <$> (xls.zip yls).mapM fun (x,y) => cmpLevel x y
      if univs != .eq then return univs
      match weakOrd.find? x, weakOrd.find? y with
      | some nx, some ny => return compare nx ny
      | none, some _ => return .gt
      | some _, none => return .lt
      | none, none => do
        let xCid := (← getContAddrConst (← getLeanConstant x)).fst
        let yCid := (← getContAddrConst (← getLeanConstant y)).fst
        return compare xCid.anon yCid.anon
    | .const .., _ => return .lt
    | _, .const .. => return .gt
    | .app xf xa, .app yf ya =>
      (· * ·) <$> cmpExpr weakOrd xf yf <*> cmpExpr weakOrd xa ya
    | .app .., _ => return .lt
    | _, .app .. => return .gt
    | .lam _ xt xb _, .lam _ yt yb _ =>
      (· * ·) <$> cmpExpr weakOrd xt yt <*> cmpExpr weakOrd xb yb
    | .lam .., _ => return .lt
    | _, .lam .. => return .gt
    | .forallE _ xt xb _, .forallE _ yt yb _ =>
      (· * ·) <$> cmpExpr weakOrd xt yt <*> cmpExpr weakOrd xb yb
    | .forallE .., _ => return .lt
    | _, .forallE .. => return .gt
    | .letE _ xt xv xb _, .letE _ yt yv yb _ =>
      (· * · * ·) <$> cmpExpr weakOrd xt yt <*> cmpExpr weakOrd xv yv <*> cmpExpr weakOrd xb yb
    | .letE .., _ => return .lt
    | _, .letE .. => return .gt
    | .lit x, .lit y =>
      return if x < y then .lt else if x == y then .eq else .gt
    | .lit .., _ => return .lt
    | _, .lit .. => return .gt
    | .proj _ nx tx, .proj _ ny ty => do
      let ts ← cmpExpr weakOrd tx ty
      return concatOrds [compare nx ny, ts]

  /-- AST comparison of two Lean definitions.
    `weakOrd` contains the best known current mutual ordering -/
  partial def cmpDef (weakOrd : Std.RBMap Name Nat compare)
    (x : Lean.DefinitionVal) (y : Lean.DefinitionVal) :
      ContAddrM Ordering := do
    let ls := compare x.levelParams.length y.levelParams.length
    let ts ← cmpExpr weakOrd x.type y.type
    let vs ← cmpExpr weakOrd x.value y.value
    return concatOrds [ls, ts, vs]

  /-- AST equality between two Lean definitions.
    `weakOrd` contains the best known current mutual ordering -/
  partial def eqDef (weakOrd : Std.RBMap Name Nat compare)
      (x : Lean.DefinitionVal) (y : Lean.DefinitionVal) : ContAddrM Bool := do
    match (← cmpDef weakOrd x y) with
    | .eq => pure true
    | _ => pure false

  /-- `sortDefs` recursively sorts a list of mutual definitions into weakly equal blocks.
    At each stage, we take as input the current best approximation of known weakly equal
    blocks as a List of blocks, hence the `List (List DefinitionVal)` as the argument type.
    We recursively take the input blocks and resort to improve the approximate known
    weakly equal blocks, obtaining a sequence of list of blocks:
    ```
    dss₀ := [startDefs]
    dss₁ := sortDefs dss₀
    dss₂ := sortDefs dss₁
    dss₍ᵢ₊₁₎ := sortDefs dssᵢ ...
    ```
    Initially, `startDefs` is simply the list of definitions we receive from `DefinitionVal.all`;
    since there is no order yet, we treat it as one block all weakly equal. On the other hand,
    at the end, there is some point where `dss₍ᵢ₊₁₎ := dssᵢ`, then we have hit a fixed point
    and we may end the sorting process. (We claim that such a fixed point exists, although
    technically we don't really have a proof.)

    On each iteration, we hope to improve our knowledge of weakly equal blocks and use that
    knowledge in the next iteration. e.g. We start with just one block with everything in it,
    but the first sort may differentiate the one block into 3 blocks. Then in the second
    iteration, we have more information than than first, since the relationship of the 3 blocks
    gives us more information; this information may then be used to sort again, turning 3 blocks
    into 4 blocks, and again 4 blocks into 6 blocks, etc, until we have hit a fixed point.
    This step is done in the computation of `newDss` and then comparing it to the original `dss`.

    Two optimizations:

    1. `names := enum dss` records the ordering information in a map for faster access.
       Directly using `List.findIdx?` on dss is slow and introduces `Option` everywhere.
       `names` is used as a custom comparison in `ds.sortByM (cmpDef names)`.
    2. `normDss/normNewDss`. We want to compare if two lists of blocks are equal.
       Technically blocks are sets and their order doesn't matter, but we have encoded
       them as lists. To fix this, we sort the list by name before comparing. Note we
       could maybe also use `List (RBTree ..)` everywhere, but it seemed like a hassle. -/
  partial def sortDefs (dss : List (List Lean.DefinitionVal)) :
      ContAddrM (List (List Lean.DefinitionVal)) := do
    let enum (ll : List (List Lean.DefinitionVal)) :=
      Std.RBMap.ofList (ll.enum.map fun (n, xs) => xs.map (·.name, n)).join
    let weakOrd := enum dss _
    let newDss ← (← dss.mapM fun ds =>
      match ds with
      | []  => unreachable!
      | [d] => return [[d]]
      | ds  => return (← List.groupByM (eqDef weakOrd) $
        ← ds.sortByM (cmpDef weakOrd))).joinM

    -- must normalize, see comments
    let normDss    := dss.map    fun ds => ds.map (·.name) |>.sort
    let normNewDss := newDss.map fun ds => ds.map (·.name) |>.sort
    if normDss == normNewDss then
      return newDss
    else
      sortDefs newDss

end

/-- Iterates over a list of `Lean.ConstantInfo`, triggering their content-addressing -/
def contAddrM (delta : List Lean.ConstantInfo) : ContAddrM Unit := do
  let log := (← read).log
  for const in delta do
    let (_, c) ← getContAddrConst const
    if log then
      IO.println "\n========================================="
      IO.println    const.name
      IO.println   "========================================="
      IO.println $  PrintLean.printLeanConst const
      IO.println   "========================================="
      IO.println $ ← PrintYatima.printYatimaConst (← derefConst c)
      IO.println   "=========================================\n"
  (← get).cache.forM fun _ (cid, idx) => do
    match Ipld.primCidsMap.find? cid.anon.data.toString with
    | none    => pure ()
    | some pc =>
      modify fun stt => { stt with tcStore := { stt.tcStore with
      primIdxs    := stt.tcStore.primIdxs.insert pc idx
      idxsToPrims := stt.tcStore.idxsToPrims.insert idx pc } }

/--
Content-addresses the "delta" of a file, that is, the content that is added on
top of what is imported by it.

Important: constants with open references in their expressions are filtered out.
Open references are variables that point to names which aren't present in the
`Lean.ConstMap`.
-/
def contAddr (filePath : System.FilePath) (log : Bool := false)
    (stt : ContAddrState := default) : IO $ Except ContAddrError ContAddrState := do
  let env ← Lean.runFrontend filePath
  let constants := env.constants.patchUnsafeRec
  let delta := constants.map₂.filter fun n _ => !n.isInternal
  ContAddrM.run (.init constants log) stt (contAddrM (delta.toList.map (·.2)))

end Yatima.ContAddr
