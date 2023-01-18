import Yatima2.Lean.Utils
import Yatima2.ContAddr.ContAddrM

/-- Move to YatimaStdLib -/
instance : HMul Ordering Ordering Ordering where hMul
  | .gt, _ => .gt
  | .lt, _ => .lt
  | .eq, x => x

/-- Move to YatimaStdLib -/
def concatOrds : List Ordering → Ordering :=
  List.foldl (fun x y => x * y) .eq

namespace Yatima.ContAddr

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
  addToStore $ .univ anon meta

/-- Retrieves a Lean constant from the environment by its name -/
def getLeanConstant (name : Lean.Name) : ContAddrM Lean.ConstantInfo := do
  match (← read).constMap.find? name with
  | some const => pure const
  | none => throw $ .unknownConstant name

mutual

partial def getContAddrConst (const : Lean.ConstantInfo) :
    ContAddrM $ Hash × Hash := do
  match (← get).env.consts.find? const.name with
  | some c => pure c
  | none   => contAddrConst const

partial def contAddrConst : Lean.ConstantInfo → ContAddrM (Hash × Hash)
  | .defnInfo val => withLevelsAndReset val.levelParams $ contAddrDefinition val
  | _ => sorry

partial def contAddrDefinition (struct : Lean.DefinitionVal) :
    ContAddrM (Hash × Hash) := do
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
  let definitionsMeta := definitions.map fun ds => ds.map Prod.snd
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
    addToEnv defnMeta.name hashes
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
    ⟨defn.name, defn.levelParams, typeHashes.2, valueHashes.2⟩
  )

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
    match expr with
      | .bvar idx => match (← read).bindCtx.get? idx with
        -- Bound variables must be in the bind context
        | some name => addToStore $ .expr (.var idx []) (.var name none [])
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
        | some (i, i?) => -- recursing!
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
      let xCid := (← getContAddrConst (← getLeanConstant x)).1
      let yCid := (← getContAddrConst (← getLeanConstant y)).1
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
def contAddrM (delta : List Lean.ConstantInfo) : ContAddrM Unit :=
  delta.forM (discard $ getContAddrConst ·)

/--
Content-addresses the "delta" of an environment, that is, the content that is
added on top of the imports.

Important: constants with open references in their expressions are filtered out.
Open references are variables that point to names which aren't present in the
`Lean.ConstMap`.
-/
def contAddr (env : Lean.Environment) (stt : ContAddrState := default) :
    Except ContAddrError ContAddrState :=
  let constants := env.constants.patchUnsafeRec
  let delta := constants.map₂.filter fun n _ => !n.isInternal
  ContAddrM.run (.init constants) stt (contAddrM $ delta.toList.map (·.2))

end Yatima.ContAddr
