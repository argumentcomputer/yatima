import Yatima.Lean.Utils
import Yatima.ContAddr.ContAddrM
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
def contAddrUniv : Lean.Level → ContAddrM Univ
  | .zero => pure .zero
  | .succ u => return .succ (← contAddrUniv u)
  | .max a b  => return .max  (← contAddrUniv a) (← contAddrUniv b)
  | .imax a b => return .imax (← contAddrUniv a) (← contAddrUniv b)
  | .param name => do
    let lvls := (← read).univCtx
    match lvls.indexOf? name with
    | some n => pure $ .var n
    | none   => throw $ .levelNotFound name lvls
  | l@(.mvar ..) => throw $ .unfilledLevelMetavariable l

/-- Retrieves a Lean constant from the environment by its name -/
def getLeanConstant (name : Lean.Name) : ContAddrM Lean.ConstantInfo := do
  match (← read).constMap.find? name with
  | some const => pure const
  | none => throw $ .unknownConstant name

def isInternalRec (expr : Lean.Expr) (name : Lean.Name) : Bool :=
  match expr with
  | .forallE _ t e _  => match e with
    | .forallE ..  => isInternalRec e name
    | _ => isInternalRec t name -- t is the major premise
  | .app e .. => isInternalRec e name
  | .const n .. => n == name
  | _ => false

mutual

partial def contAddrConst (const : Lean.ConstantInfo) : ContAddrM Lurk.F := do
  match (← get).env.consts.find? const.name with
  | some hash => pure hash
  | none => match const with
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
      let obj ← match const with
        | .defnInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ => unreachable!
        | .axiomInfo val =>
          pure $ .axiom ⟨val.levelParams.length, ← contAddrExpr val.type⟩
        | .thmInfo val =>
          -- Theorems are never truly recursive
          pure $ .theorem ⟨val.levelParams.length, ← contAddrExpr val.type,
            ← contAddrExpr val.value⟩
        | .opaqueInfo val =>
          let recrs := .single val.name 0
          pure $ .opaque ⟨val.levelParams.length, ← contAddrExpr val.type,
            ← withRecrs recrs $ contAddrExpr val.value⟩
        | .quotInfo val =>
          pure $ .quotient ⟨val.levelParams.length, ← contAddrExpr val.type, val.kind⟩
      let hash ← commit obj
      addToEnv const.name hash
      return hash

partial def contAddrDefinition (struct : Lean.DefinitionVal) : ContAddrM Lurk.F := do
  -- If the mutual size is one, simply content address the single definition
  if struct.all matches [_] then
    let hash ← commit $ .definition
      (← withRecrs (.single struct.name 0) $ definitionToIR struct)
    addToEnv struct.name hash
    return hash

  -- Collecting and sorting all definitions in the mutual block
  let mutualDefs ← struct.all.mapM fun name => do
    match ← getLeanConstant name with
    | .defnInfo defn => pure defn
    | const => throw $ .invalidConstantKind const.name "definition" const.ctorName
  let mutualDefs ← sortDefs [mutualDefs]

  -- Building the `recrCtx`
  let mut recrCtx := default
  for (i, ds) in mutualDefs.enum do
    for d in ds do
      recrCtx := recrCtx.insert d.name i

  let definitions ← withRecrs recrCtx $ mutualDefs.mapM (·.mapM definitionToIR)

  -- Building and storing the block
  let definitionsIr := (definitions.map (match ·.head? with
    | some d => [d] | none => [])).join
  let blockHash ← commit $ .mutDefBlock definitionsIr

  -- While iterating on the definitions from the mutual block, we need to track
  -- the correct objects to return
  let mut ret? : Option Lurk.F := none

  for name in struct.all do
    -- Storing and caching the definition projection
    -- Also adds the constant to the array of constants
    let some idx := recrCtx.find? name | throw $ .cantFindMutDefIndex name
    let hash ← commit $ .definitionProj ⟨blockHash, idx⟩
    addToEnv name hash
    if struct.name == name then ret? := some hash

  match ret? with
  | some ret => return ret
  | none => throw $ .constantNotContentAddressed struct.name

partial def definitionToIR (defn : Lean.DefinitionVal) : ContAddrM Definition :=
  return ⟨defn.levelParams.length, ← contAddrExpr defn.type,
    ← contAddrExpr defn.value, defn.safety == .partial⟩

/--
Content-addresses an inductive and all inductives in the mutual block as a
mutual block, even if the inductive itself is not in a mutual block.

Content-addressing an inductive involves content-addressing its associated
constructors and recursors, hence the lenght of this function.
-/
partial def contAddrInductive (initInd : Lean.InductiveVal) : ContAddrM Lurk.F := do
  -- `mutualConsts` is the list of the names of all constants associated with an inductive block
  -- it has the form: ind₁ ++ ctors₁ ++ recrs₁ ++ ... ++ indₙ ++ ctorsₙ ++ recrsₙ
  let mut inds := []
  let mut indCtors := []
  let mut indRecs := []
  let mut nameData : RBMap Name (List Name × List Name) compare := .empty
  for indName in initInd.all do
    match ← getLeanConstant indName with
    | .inductInfo ind =>
      let indRecrs := ((← read).constMap.childrenOfWith ind.name
        fun c => match c with | .recInfo _ => true | _ => false).map (·.name)
      inds := inds ++ [indName]
      indCtors := indCtors ++ ind.ctors
      indRecs := indRecs ++ indRecrs
      nameData := nameData.insert indName (ind.ctors, indRecrs)
    | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName

  -- `mutualConsts` is the list of the names of all constants associated with an
  -- inductive block: the inductives themselves, the constructors and the recursors
  let mutualConsts := inds ++ indCtors ++ indRecs

  let recrCtx := mutualConsts.enum.foldl (init := default)
    fun acc (i, n) => acc.insert n i

  -- This part will build the inductive block and add all inductives,
  -- constructors and recursors to `consts`
  let irInds ← initInd.all.mapM fun name => do match ← getLeanConstant name with
    | .inductInfo ind => withRecrs recrCtx do pure $ (← inductiveToIR ind)
    | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
  let blockHash ← commit $ .mutIndBlock irInds

  -- While iterating on the inductives from the mutual block, we need to track
  -- the correct objects to return
  let mut ret? : Option Lurk.F := none
  for (indIdx, indName) in initInd.all.enum do
    -- Store and cache inductive projections
    let name := indName
    let hash ← commit $ .inductiveProj ⟨blockHash, indIdx⟩
    addToEnv name hash
    if name == initInd.name then ret? := some hash

    let some (ctors, recrs) := nameData.find? indName 
      | throw $ .cantFindMutDefIndex indName

    for (ctorIdx, ctorName) in ctors.enum do
      -- Store and cache constructor projections
      let hashes ← commit $ .constructorProj ⟨blockHash, indIdx, ctorIdx⟩
      addToEnv ctorName hashes

    for (recrIdx, recrName) in recrs.enum do
      -- Store and cache recursor projections
      let hashes ← commit $ .recursorProj ⟨blockHash, indIdx, recrIdx⟩
      addToEnv recrName hashes

  match ret? with
  | some ret => return ret
  | none => throw $ .constantNotContentAddressed initInd.name

partial def inductiveToIR (ind : Lean.InductiveVal) : ContAddrM Inductive := do
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
  let (struct, unit) ← if ind.isRec || ind.numIndices != 0 then pure (false, false) else
    match ctors with
    -- Structures can only have one constructor
    | [ctor] => pure (true, ctor.fields == 0)
    | _ => pure (false, false)
  return ⟨ind.levelParams.length, ← contAddrExpr ind.type, ind.numParams, ind.numIndices,
    -- NOTE: for the purpose of extraction, the order of `ctors` and `recs` MUST
    -- match the order used in `recrCtx`
    ctors, recs, ind.isRec, ind.isReflexive, struct, unit⟩

partial def internalRecToIR (ctors : List Lean.Name) :
    Lean.ConstantInfo → ContAddrM (Recursor × List Constructor)
  | .recInfo rec => withLevels rec.levelParams do
    let typ ← contAddrExpr rec.type
    let (retCtors, retRules) ← rec.rules.foldrM (init := ([], []))
      fun r (retCtors, retRules) => do
        if ctors.contains r.ctor then
          let (ctor, rule) ← recRuleToIR r
          pure $ (ctor :: retCtors, rule :: retRules)
        else pure (retCtors, retRules) -- this is an external recursor rule
    let recr := ⟨rec.levelParams.length, typ, rec.numParams, rec.numIndices,
      rec.numMotives, rec.numMinors, retRules, rec.k, true⟩
    return (recr, retCtors)
  | const => throw $ .invalidConstantKind const.name "recursor" const.ctorName

partial def recRuleToIR (rule : Lean.RecursorRule) : ContAddrM $ Constructor × RecursorRule := do
  let rhs ← contAddrExpr rule.rhs
  match ← getLeanConstant rule.ctor with
  | .ctorInfo ctor => withLevels ctor.levelParams do
    let typ ← contAddrExpr ctor.type
    let ctor := ⟨ctor.levelParams.length, typ, ctor.cidx, ctor.numParams, ctor.numFields⟩
    pure (ctor, ⟨rule.nfields, rhs⟩)
  | const => throw $ .invalidConstantKind const.name "constructor" const.ctorName

partial def externalRecToIR : Lean.ConstantInfo → ContAddrM Recursor
  | .recInfo rec => withLevels rec.levelParams do
    let typ ← contAddrExpr rec.type
    let rules ← rec.rules.mapM externalRecRuleToIR
    return ⟨rec.levelParams.length, typ, rec.numParams, rec.numIndices,
      rec.numMotives, rec.numMinors, rules, rec.k, false⟩
  | const => throw $ .invalidConstantKind const.name "recursor" const.ctorName

partial def externalRecRuleToIR (rule : Lean.RecursorRule) : ContAddrM RecursorRule :=
  return ⟨rule.nfields, ← contAddrExpr rule.rhs⟩

/--
Content-addresses a Lean expression and adds it to the store.

Constants are the tricky case, for which there are two possibilities:
* The constant belongs to `recrCtx`, representing a recursive call. Those are
encoded as variables with indexes that go beyond the bind indexes
* The constant doesn't belong to `recrCtx`, meaning that it's not a recursion
and thus we can contAddr the actual constant right away
-/
partial def contAddrExpr : Lean.Expr → ContAddrM Expr
  | .mdata _ e => contAddrExpr e
  | expr => match expr with
    | .bvar idx => do match (← read).bindCtx.get? idx with
      -- Bound variables must be in the bind context
      | some _ => return .var idx []
      | none => throw $ .invalidBVarIndex idx
    | .sort lvl => return .sort $ ← contAddrUniv lvl
    | .const name lvls => do
      let univs ← lvls.mapM contAddrUniv
      match (← read).recrCtx.find? name with
      | some i => -- recursing!
        let idx := (← read).bindCtx.length + i
        return .var idx univs
      | none => return .const (← contAddrConst $ ← getLeanConstant name) univs
    | .app fnc arg => return .app (← contAddrExpr fnc) (← contAddrExpr arg)
    | .lam name typ bod _ =>
      return .lam (← contAddrExpr typ) (← withBinder name $ contAddrExpr bod)
    | .forallE name dom img _ =>
      return .pi (← contAddrExpr dom) (← withBinder name $ contAddrExpr img)
    | .letE name typ exp bod _ =>
      return .letE (← contAddrExpr typ) (← contAddrExpr exp)
        (← withBinder name $ contAddrExpr bod)
    | .lit lit => return .lit lit
    | .proj _ idx exp => return .proj idx (← contAddrExpr exp)
    | .fvar ..  => throw $ .freeVariableExpr expr
    | .mvar ..  => throw $ .metaVariableExpr expr
    | .mdata .. => throw $ .metaDataExpr expr

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
    | none, none =>
      return compare (← contAddrConst $ ← getLeanConstant x)
        (← contAddrConst $ ← getLeanConstant y)
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

/-- Iterates over a list of `Lean.ConstantInfo`, triggering their content-addressing -/
def contAddrM (delta : List Lean.ConstantInfo) : ContAddrM Unit :=
  delta.forM fun c => if !c.isUnsafe then discard $ contAddrConst c else pure ()

/--
Content-addresses the "delta" of an environment, that is, the content that is
added on top of the imports.

Important: constants with open references in their expressions are filtered out.
Open references are variables that point to names which aren't present in the
`Lean.ConstMap`.
-/
def contAddr (constMap : Lean.ConstMap) (delta : List Lean.ConstantInfo) (yenv : Env)
    (quick persist : Bool) : IO $ Except ContAddrError ContAddrState := do
  let persist := if quick then false else persist
  match ← StateT.run (ReaderT.run (contAddrM delta)
    (.init constMap quick persist)) (.init yenv) with
  | (.ok _, stt) => return .ok stt
  | (.error e, _) => return .error e

end Yatima.ContAddr
