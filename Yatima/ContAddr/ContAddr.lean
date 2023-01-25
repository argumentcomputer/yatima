import Yatima.Lean.Utils
import Yatima.ContAddr.ContAddrM
import Yatima.ContAddr.ToLDON
import YatimaStdLib.RBMap

namespace Yatima.ContAddr

scoped instance : HMul Ordering Ordering Ordering where hMul
  | .gt, _ => .gt
  | .lt, _ => .lt
  | .eq, x => x

def concatOrds : List Ordering → Ordering :=
  List.foldl (· * ·) .eq

open IR
open Std (RBMap)

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

/-- Content-addresses a Lean universe level and adds it to the store -/
def contAddrUniv (l : Lean.Level) : ContAddrM (Hash × Hash) := do
  let (anon, meta) ← match l with
    | .zero => pure (.zero, .zero)
    | .succ n =>
      let (anon, meta) ← contAddrUniv n
      pure (.succ anon, .succ meta)
    | .max a b  =>
      let (aAnon, aMeta) ← contAddrUniv a
      let (bAnon, bMeta) ← contAddrUniv b
      pure (.max aAnon bAnon, .max aMeta bMeta)
    | .imax a b  =>
      let (aAnon, aMeta) ← contAddrUniv a
      let (bAnon, bMeta) ← contAddrUniv b
      pure (.imax aAnon bAnon, .max aMeta bMeta)
    | .param name =>
      let lvls := (← read).univCtx
      match lvls.indexOf? name with
      | some n => pure (.var n, .var name)
      | none   => throw $ .levelNotFound name lvls
    | .mvar .. => throw $ .unfilledLevelMetavariable l
  addToStore $ .univ anon meta

/-- Retrieves a Lean constant from the environment by its name -/
def getLeanConstant (name : Lean.Name) : ContAddrM Lean.ConstantInfo := do
  match (← read).constMap.find? name with
  | some const => pure const
  | none => throw $ .unknownConstant name

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

partial def contAddrConst (const : Lean.ConstantInfo) :
    ContAddrM $ Hash × Hash := do
  match (← get).env.irHashes.find? const.name with
  | some c => pure c
  | none   => match const with
    | .defnInfo val => withLevelsAndReset val.levelParams $ contAddrDefinition val
    | .inductInfo val => withLevelsAndReset val.levelParams $ contAddrInductive val
    | .ctorInfo val => do
      match ← getLeanConstant val.induct with
      | .inductInfo ind => discard $ contAddrConst (.inductInfo ind)
      | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
      contAddrConst const
    | .recInfo val => do
      match ← getLeanConstant val.getInduct with
      | .inductInfo ind => discard $ contAddrConst (.inductInfo ind)
      | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
      contAddrConst const
    -- The rest adds the constants to the cache one by one
    | const => withLevelsAndReset const.levelParams do
      let (anon, meta) ← match const with
        | .defnInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ => unreachable!
        | .axiomInfo val =>
          let (typAnon, typMeta) ← contAddrExpr val.type
          pure (.axiom ⟨val.levelParams.length, typAnon, !val.isUnsafe⟩,
            .axiom ⟨val.name, val.levelParams, typMeta⟩)
        | .thmInfo val =>
          -- Theorems are never truly recursive
          let (typAnon, typMeta) ← contAddrExpr val.type
          let (valAnon, valMeta) ← contAddrExpr val.value
          pure (.theorem ⟨val.levelParams.length, typAnon, valAnon⟩,
            .theorem ⟨val.name, val.levelParams, typMeta, valMeta⟩)
        | .opaqueInfo val =>
          let (typAnon, typMeta) ← contAddrExpr val.type
          let recrs := .single val.name (0, some 0)
          let (valAnon, valMeta) ← withRecrs recrs $ contAddrExpr val.value
          pure (.opaque ⟨val.levelParams.length, typAnon, valAnon, !val.isUnsafe⟩,
            .opaque ⟨val.name, val.levelParams, typMeta, valMeta⟩)
        | .quotInfo val =>
          let (typAnon, typMeta) ← contAddrExpr val.type
          pure (.quotient ⟨val.levelParams.length, typAnon, val.kind⟩,
            .quotient ⟨val.name, val.levelParams, typMeta⟩)
      let hashes ← addToStore $ .const anon meta
      addIRHashesToEnv const.name hashes
      return hashes

partial def contAddrDefinition (struct : Lean.DefinitionVal) :
    ContAddrM $ Hash × Hash := do
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

  -- Building the `recrCtx`
  let mut recrCtx := RBMap.empty
  for (i, ds) in mutualDefs.enum do
    for (j, d) in ds.enum do
      recrCtx := recrCtx.insert d.name (i, some j)

  let definitions ← withRecrs recrCtx $ mutualDefs.mapM (·.mapM definitionToIR)

  -- Building and storing the block
  let definitionsAnon := (definitions.map (match ·.head? with
    | some d => [d.1] | none => [])).join
  let definitionsMeta := definitions.map fun ds => ds.map (·.2)
  let blockHashes ← addToStore $
    .const (.mutDefBlock definitionsAnon) (.mutDefBlock definitionsMeta)

  -- While iterating on the definitions from the mutual block, we need to track
  -- the correct objects to return
  let mut ret? : Option (Hash × Hash) := none

  for (i, (defnAnon, defnMeta)) in definitions.join.enum do
    -- Storing and caching the definition projection
    -- Also adds the constant to the array of constants
    let some (idx, _) := recrCtx.find? defnMeta.name | throw $ .cantFindMutDefIndex defnMeta.name
    let valueAnon := .definitionProj ⟨defnAnon.lvls, defnAnon.type, blockHashes.1, idx⟩
    let valueMeta := .definitionProj ⟨defnMeta.name, defnMeta.lvls, defnMeta.type, blockHashes.2, i⟩
    let hashes ← addToStore $ .const valueAnon valueMeta
    addIRHashesToEnv defnMeta.name hashes
    if defnMeta.name == struct.name then ret? := some hashes

  match ret? with
  | some ret => return ret
  | none => throw $ .constantNotContentAddressed struct.name

partial def definitionToIR (defn : Lean.DefinitionVal) :
    ContAddrM (DefinitionAnon × DefinitionMeta) := do
  let typeHashes ← contAddrExpr defn.type
  let valueHashes ← contAddrExpr defn.value
  return (
    ⟨defn.levelParams.length, typeHashes.1, valueHashes.1, defn.safety⟩,
    ⟨defn.name, defn.levelParams, typeHashes.2, valueHashes.2⟩)

/--
Content-addresses an inductive and all inductives in the mutual block as a
mutual block, even if the inductive itself is not in a mutual block.

Content-addressing an inductive involves content-addressing its associated
constructors and recursors, hence the lenght of this function.
-/
partial def contAddrInductive (initInd : Lean.InductiveVal) :
    ContAddrM $ Hash × Hash := do
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

  -- `mutualConsts` is the list of the names of all constants associated with an
  -- inductive block: the inductives themselves, the constructors and the recursors
  let mutualConsts := inds ++ indCtors ++ indRecs

  let recrCtx := mutualConsts.enum.foldl (init := default)
    fun acc (i, n) => acc.insert n (i, none)

  -- This part will build the inductive block and add all inductives,
  -- constructors and recursors to `consts`
  let irInds ← initInd.all.mapM fun name => do match ← getLeanConstant name with
    | .inductInfo ind => withRecrs recrCtx do pure $ (← inductiveToIR ind)
    | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
  let (blockAnon, blockMeta) ← addToStore $
    .const (.mutIndBlock $ irInds.map (·.1)) (.mutIndBlock $ irInds.map (·.2))

  -- While iterating on the inductives from the mutual block, we need to track
  -- the correct objects to return
  let mut ret? : Option (Hash × Hash) := none

  for (indIdx, ⟨indAnon, indMeta⟩) in irInds.enum do
    -- Store and cache inductive projections
    let name := indMeta.name
    let hashes ← addToStore $ .const
      (.inductiveProj ⟨indAnon.lvls, indAnon.type, blockAnon, indIdx⟩)
      (.inductiveProj ⟨indMeta.name, indMeta.lvls, indMeta.type, blockMeta⟩)
    addIRHashesToEnv name hashes
    if name == initInd.name then ret? := some hashes

    for (ctorIdx, (ctorAnon, ctorMeta)) in (indAnon.ctors.zip indMeta.ctors).enum do
      -- Store and cache constructor projections
      let hashes ← addToStore $ .const
        (.constructorProj ⟨ctorAnon.lvls, ctorAnon.type, blockAnon, indIdx, ctorIdx⟩)
        (.constructorProj ⟨ctorMeta.name, ctorMeta.lvls, ctorMeta.type, blockMeta⟩)
      addIRHashesToEnv ctorMeta.name hashes

    for (recrIdx, (recrAnon, recrMeta)) in (indAnon.recrs.zip indMeta.recrs).enum do
      -- Store and cache recursor projections
      let hashes ← addToStore $ .const
        (.recursorProj ⟨recrAnon.lvls, recrAnon.type, blockAnon, indIdx, recrIdx⟩)
        (.recursorProj ⟨recrMeta.name, recrMeta.lvls, recrMeta.type, blockMeta⟩)
      addIRHashesToEnv recrMeta.name hashes

  match ret? with
  | some ret => return ret
  | none => throw $ .constantNotContentAddressed initInd.name

partial def inductiveToIR (ind : Lean.InductiveVal) :
    ContAddrM $ InductiveAnon × InductiveMeta := do
  let leanRecs := (← read).constMap.childrenOfWith ind.name
    fun c => match c with | .recInfo _ => true | _ => false
  let (recs, ctors) ← leanRecs.foldrM (init := ([], []))
    fun r (recs, ctors) => match r with
      | .recInfo rv =>
        if isInternalRec rv.type ind.name then do
          let (thisRec, thisCtors) := ← internalRecToIR ind.ctors r
          pure (thisRec :: recs, thisCtors)
        else do
          let thisRec ← externalRecToIR r
          pure (thisRec :: recs, ctors)
      | _ => throw $ .nonRecursorExtractedFromChildren r.name
  let (typAnon, typMeta) ← contAddrExpr ind.type
  let indAnon := ⟨ind.levelParams.length, typAnon, ind.numParams, ind.numIndices,
    -- NOTE: for the purpose of extraction, the order of `ctors` and `recs` MUST
    -- match the order used in `recrCtx`
    ctors.map (·.1), recs.map (·.1), ind.isRec, !ind.isUnsafe, ind.isReflexive⟩
  let indMeta := ⟨ind.name, ind.levelParams, typMeta, ctors.map (·.2), recs.map (·.2)⟩
  return (indAnon, indMeta)

partial def internalRecToIR (ctors : List Lean.Name) :
  Lean.ConstantInfo → ContAddrM
    ((RecursorAnon × RecursorMeta) × (List $ ConstructorAnon × ConstructorMeta))
  | .recInfo rec => withLevels rec.levelParams do
    let (typAnon, typMeta) ← contAddrExpr rec.type
    let (retCtors, retRules) ← rec.rules.foldrM (init := ([], []))
      fun r (retCtors, retRules) => do
        if ctors.contains r.ctor then
          let (ctor, rule) ← recRuleToIR r
          pure $ (ctor :: retCtors, rule :: retRules)
        else pure (retCtors, retRules) -- this is an external recursor rule
    let recAnon := ⟨rec.levelParams.length, typAnon, rec.numParams,
      rec.numIndices, rec.numMotives, rec.numMinors, retRules.map (·.1),
      rec.k, true⟩
    let recMeta := ⟨rec.name, rec.levelParams, typMeta, retRules.map (·.2)⟩
    return ((recAnon, recMeta), retCtors)
  | const => throw $ .invalidConstantKind const.name "recursor" const.ctorName

partial def recRuleToIR (rule : Lean.RecursorRule) : ContAddrM $
    (ConstructorAnon × ConstructorMeta) × (RecursorRuleAnon × RecursorRuleMeta) := do
  let (rhsAnon, rhsMeta) ← contAddrExpr rule.rhs
  match ← getLeanConstant rule.ctor with
  | .ctorInfo ctor => withLevels ctor.levelParams do
    let (typAnon, typMeta) ← contAddrExpr ctor.type
    let ctors := (
      ⟨ctor.levelParams.length, typAnon, ctor.cidx, ctor.numParams, ctor.numFields, !ctor.isUnsafe⟩,
      ⟨ctor.name, ctor.levelParams, typMeta⟩)
    pure (ctors, (⟨rule.nfields, rhsAnon⟩, ⟨rhsMeta⟩))
  | const => throw $ .invalidConstantKind const.name "constructor" const.ctorName

partial def externalRecToIR : Lean.ConstantInfo → ContAddrM (RecursorAnon × RecursorMeta)
  | .recInfo rec => withLevels rec.levelParams do
    let (typAnon, typMeta) ← contAddrExpr rec.type
    let rules ← rec.rules.mapM externalRecRuleToIR
    return (
      ⟨rec.levelParams.length, typAnon, rec.numParams, rec.numIndices,
        rec.numMotives, rec.numMinors, rules.map (·.1), rec.k, false⟩,
      ⟨rec.name, rec.levelParams, typMeta, rules.map (·.2)⟩)
  | const => throw $ .invalidConstantKind const.name "recursor" const.ctorName

partial def externalRecRuleToIR (rule : Lean.RecursorRule) :
    ContAddrM (RecursorRuleAnon × RecursorRuleMeta) := do
  let (rhsAnon, rhsMeta) ← contAddrExpr rule.rhs
  return (⟨rule.nfields, rhsAnon⟩, ⟨rhsMeta⟩)

/--
Content-addresses a Lean expression and adds it to the store.

Constants are the tricky case, for which there are two possibilities:
* The constant belongs to `recrCtx`, representing a recursive call. Those are
encoded as variables with indexes that go beyond the bind indexes
* The constant doesn't belong to `recrCtx`, meaning that it's not a recursion
and thus we can contAddr the actual constant right away
-/
partial def contAddrExpr : Lean.Expr → ContAddrM (Hash × Hash)
  | .mdata _ e => contAddrExpr e
  | expr => do
    let (anon, meta) ← match expr with
      | .bvar idx => match (← read).bindCtx.get? idx with
        -- Bound variables must be in the bind context
        | some name => pure (.var idx [], .var name none [])
        | none => throw $ .invalidBVarIndex idx
      | .sort lvl =>
        let (anon, meta) ← contAddrUniv lvl
        pure (.sort anon, .sort meta)
      | .const name lvls =>
        let (univHashesAnon, univHashesMeta) ← lvls.foldrM (init := ([], []))
          fun lvl (anons, metas) => do
            let (anon, meta) ← contAddrUniv lvl
            pure (anon :: anons, meta :: metas)
        match (← read).recrCtx.find? name with
        | some (i, i?) => -- recursing!
          let idx := (← read).bindCtx.length + i
          pure (.var idx univHashesAnon, .var name i? univHashesMeta)
        | none =>
          let (anon, meta) ← contAddrConst (← getLeanConstant name)
          pure (.const anon univHashesAnon, .const meta univHashesMeta)
      | .app fnc arg =>
        let (fncAnon, fncMeta) ← contAddrExpr fnc
        let (argAnon, argMeta) ← contAddrExpr arg
        pure (.app fncAnon argAnon, .app fncMeta argMeta)
      | .lam name typ bod bnd =>
        let (typAnon, typMeta) ← contAddrExpr typ
        let (bodAnon, bodMeta) ← withBinder name $ contAddrExpr bod
        pure (.lam typAnon bodAnon, .lam name bnd typMeta bodMeta)
      | .forallE name dom img bnd =>
        let (domAnon, domMeta) ← contAddrExpr dom
        let (imgAnon, imgMeta) ← withBinder name $ contAddrExpr img
        pure (.pi domAnon imgAnon, .pi name bnd domMeta imgMeta)
      | .letE name typ exp bod _ =>
        let (typAnon, typMeta) ← contAddrExpr typ
        let (expAnon, expMeta) ← contAddrExpr exp
        let (bodAnon, bodMeta) ← withBinder name $ contAddrExpr bod
        pure (.letE typAnon expAnon bodAnon, .letE name typMeta expMeta bodMeta)
      | .lit lit => pure (.lit lit, .lit)
      | .proj _ idx exp =>
        let (expAnon, expMeta) ← contAddrExpr exp
        pure (.proj idx expAnon, .proj expMeta)
      | .fvar ..  => throw $ .freeVariableExpr expr
      | .mvar ..  => throw $ .metaVariableExpr expr
      | .mdata .. => throw $ .metaDataExpr expr
    addToStore $ .expr anon meta

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
      let xCid := (← contAddrConst (← getLeanConstant x)).1
      let yCid := (← contAddrConst (← getLeanConstant y)).1
      return compare xCid yCid
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
@[inline] partial def eqDef (weakOrd : Std.RBMap Name Nat compare)
    (x y : Lean.DefinitionVal) : ContAddrM Bool :=
  return (← cmpDef weakOrd x y) == .eq

/--
`sortDefs` recursively sorts a list of mutual definitions into weakly equal blocks.
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
    could maybe also use `List (RBTree ..)` everywhere, but it seemed like a hassle.
-/
partial def sortDefs (dss : List (List Lean.DefinitionVal)) :
    ContAddrM (List (List Lean.DefinitionVal)) := do
  let enum (ll : List (List Lean.DefinitionVal)) :=
    Std.RBMap.ofList (ll.enum.map fun (n, xs) => xs.map (·.name, n)).join
  let weakOrd := enum dss _
  let newDss ← (← dss.mapM fun ds =>
    match ds with
    | []  => unreachable!
    | [d] => pure [[d]]
    | ds  => do pure $ (← List.groupByM (eqDef weakOrd) $
      ← ds.sortByM (cmpDef weakOrd))).joinM

  -- must normalize, see comments
  let normDss    := dss.map    fun ds => ds.map (·.name) |>.sort
  let normNewDss := newDss.map fun ds => ds.map (·.name) |>.sort
  if normDss == normNewDss then return newDss
  else sortDefs newDss

end

open Lurk

partial def mkTCUniv (hash : Hash) : ContAddrM TC.Univ := do
  let store := (← get).store
  match store.tcUniv.find? hash with
  | some u => pure u
  | none =>
    let u ← match store.irUnivAnon.find? hash with
      | none => throw sorry
      | some .zero => pure .zero
      | some $ .succ u => pure $ .succ (← mkTCUniv u)
      | some $ .max u v => pure $ .max (← mkTCUniv u) (← mkTCUniv v)
      | some $ .imax u v => pure $ .imax (← mkTCUniv u) (← mkTCUniv v)
      | some $ .var n => pure $ .var n
    persistData (hash, u) UNIVDIR
    modifyGet fun stt => (u, { stt with store := { stt.store with
      tcUniv := stt.store.tcUniv.insert hash u } })

mutual

partial def mkTCExpr (hash : Hash) : ContAddrM TC.Expr := do
  let store := (← get).store
  match store.tcExpr.find? hash with
  | some e => pure e
  | none =>
    let e ← match store.irExprAnon.find? hash with
      | none => throw sorry
      | some $ .var i us => sorry
      | some $ .sort u => pure $ .sort (← mkTCUniv u)
      | some $ .const c us =>
        pure $ .const (← commitTCConst (← mkTCConst c)) (← us.mapM mkTCUniv)
      | some $ .app x y => pure $ .app (← mkTCExpr x) (← mkTCExpr y)
      | some $ .lam x y => pure $ .lam (← mkTCExpr x) (← mkTCExpr y)
      | some $ .pi  x y => pure $ .pi  (← mkTCExpr x) (← mkTCExpr y)
      | some $ .letE x y z => pure $ .letE (← mkTCExpr x) (← mkTCExpr y) (← mkTCExpr z)
      | some $ .lit l => pure $ .lit l
      | some $ .proj n e => pure $ .proj n (← mkTCExpr e)
    persistData (hash, e) EXPRDIR
    modifyGet fun stt => (e, { stt with store := { stt.store with
      tcExpr := stt.store.tcExpr.insert hash e } })

partial def mkTCCtor : IR.ConstructorAnon → ContAddrM TC.Constructor
| ⟨lvls, typeHash, ids, params, fields, safe⟩ => do pure ⟨lvls, ← mkTCExpr typeHash, ids, params, fields, safe⟩

partial def mkTCInd : IR.InductiveAnon → ContAddrM TC.Inductive
| ⟨lvls, type, params, indices, ctors, _, recr, safe, refl⟩ => do
    -- Structures can't be recursive nor have indices
    let (struct, unit) ← if recr || indices != 0 then pure (none, false) else
      match ctors with
      -- Structures can only have one constructor
      | [ctor] => do
        let f ← commitTCConst $ .constructor $ ← mkTCCtor ctor
        pure $ (some f, ctor.fields == 0)
      | _ => pure (none, false)
    pure $ ⟨lvls, ← mkTCExpr type, params, indices, ← ctors.mapM mkTCCtor, recr, safe, refl, struct, unit⟩

partial def mkTCConst (hash : Hash) : ContAddrM TC.Const := do
  match (← get).store.tcConst.find? hash with
  | some c => pure c
  | none =>
    let c ← match (← get).store.irConstAnon.find? hash with
      | none => throw sorry
      | some $ .axiom x => pure $ .axiom ⟨x.lvls, ← mkTCExpr x.type, x.safe⟩
      | some $ .theorem x => pure $ .theorem ⟨x.lvls, ← mkTCExpr x.type, ← mkTCExpr x.value⟩
      | some $ .opaque x => pure $ .opaque ⟨x.lvls, ← mkTCExpr x.type, ← mkTCExpr x.value, x.safe⟩
      | some $ .quotient x => pure $ .quotient ⟨x.lvls, ← mkTCExpr x.type, x.kind⟩
      | some $ .inductiveProj x =>
        match (← get).store.irConstAnon.find? x.block with
          | none => throw sorry
          | some $ .mutIndBlock inds =>
            let some ind := inds.get? x.idx | throw sorry
            pure $ .inductive $ ← mkTCInd ind
          | _ => throw sorry
      | some $ .constructorProj x =>
        match (← get).store.irConstAnon.find? x.block with
          | none => throw sorry
          | some $ .mutIndBlock inds =>
            let some ind := inds.get? x.idx | throw sorry
            let some ⟨lvls, type, idx, params, fields, safe⟩ := ind.ctors.get? x.idx | throw sorry
            pure $ .constructor ⟨lvls, ← mkTCExpr type, idx, params, fields, safe⟩
          | _ => throw sorry
      | some $ .recursorProj x =>
        match (← get).store.irConstAnon.find? x.block with
          | none => throw sorry
          | some $ .mutIndBlock inds =>
            let some ind := inds.get? x.idx | throw sorry
            let indF ← commitTCConst $ .inductive $ ← mkTCInd ind
            let some ⟨lvls, type, params, indices, motives, minors, rules, isK, internal⟩ := ind.recrs.get? x.idx | throw sorry
            pure $ .recursor ⟨lvls, ← mkTCExpr type, params, indices, motives, minors, sorry, isK, internal, indF, sorry⟩
          | _ => throw sorry
      | some $ .definitionProj x =>
        match (← get).store.irConstAnon.find? x.block with
          | none => throw sorry
          | some $ .mutDefBlock defs =>
            let some ⟨lvls, type, value, safety⟩ := defs.get? x.idx | throw sorry
            pure $ .definition ⟨lvls, ← mkTCExpr type, ← mkTCExpr value, safety, sorry⟩
          | _ => throw sorry
      | some $ .mutDefBlock _ | some $ .mutIndBlock _ => throw sorry
    persistData (hash, c) CONSTDIR
    modifyGet fun stt => (c, { stt with store := { stt.store with
      tcConst := stt.store.tcConst.insert hash c } })

partial def commitTCConst (c : TC.Const) : ContAddrM F := do
  match (← get).store.commits.find? c with
  | some f => pure f
  | none =>
    -- this is expensive
    let (f, encStt) := c.toLDON |>.commit (← get).store.ldonHashState
    persistData (c, f) COMMITSDIR
    modifyGet fun stt => (f, { stt with store := { stt.store with
      commits := stt.store.commits.insert c f
      ldonHashState := encStt } })

end

/-- Iterates over a list of `Lean.ConstantInfo`, triggering their content-addressing -/
def contAddrM (delta : List Lean.ConstantInfo) : ContAddrM Unit := do
  let anons := (← delta.mapM contAddrConst).map (·.1)
  -- let consts ← anons.mapM mkTCConst
  -- let names := delta.map (·.name)
  -- (names.zip consts).forM fun (n, c) => do addTCHashToEnv n (← commitTCConst c)
  -- persistData (← get).store.ldonHashState LDONHASHCACHE false

/--
Content-addresses the "delta" of an environment, that is, the content that is
added on top of the imports.

Important: constants with open references in their expressions are filtered out.
Open references are variables that point to names which aren't present in the
`Lean.ConstMap`.
-/
def contAddr (constants : Lean.ConstMap) (delta : List Lean.ConstantInfo)
    (stt : ContAddrState := default) : IO $ Except ContAddrError ContAddrState :=
  ContAddrM.run (.init constants) stt (contAddrM delta)

end Yatima.ContAddr
