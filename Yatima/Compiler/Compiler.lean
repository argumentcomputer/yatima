import Yatima.Compiler.Printing
import Yatima.Ipld.ToIpld
import YatimaStdLib.RBMap
import Yatima.Ipld.PrimOps

namespace Yatima.Compiler

open Std (RBMap)

/-- Gets a constant from the array of constants -/
def derefConst (idx : ConstIdx) : CompileM Const := do
  let consts := (← get).consts
  let size := consts.size
  if h : idx < size then
    return consts[idx]'h
  else
    throw $ .invalidConstantIndex idx size

/-- Retrieves a Lean constant from the environment by its name -/
def getLeanConstant (name : Lean.Name) : CompileM Lean.ConstantInfo := do
  match (← read).constMap.find? name with
  | some const => pure const
  | none => throw $ .unknownConstant name

/-- Compiles a Lean universe level and adds it to the store -/
def compileUniv (l : Lean.Level) : CompileM (UnivCid × Univ) := do
  let (value, univ) ← match l with
    | .zero      => do
      let value : Ipld.Both Ipld.Univ := ⟨ .zero, .zero ⟩
      pure (value, .zero)
    | .succ n    => do
      let (univCid, univ) ← compileUniv n
      let value : Ipld.Both Ipld.Univ := ⟨ .succ univCid.anon, .succ univCid.meta ⟩
      pure (value, .succ univ)
    | .max  a b  => do
      let (univACid, univA) ← compileUniv a
      let (univBCid, univB) ← compileUniv b
      let value : Ipld.Both Ipld.Univ := ⟨ .max univACid.anon univBCid.anon, .max univACid.meta univBCid.meta ⟩
      pure (value, .max univA univB)
    | .imax  a b  => do
      let (univACid, univA) ← compileUniv a
      let (univBCid, univB) ← compileUniv b
      let value : Ipld.Both Ipld.Univ := ⟨ .imax univACid.anon univBCid.anon, .imax univACid.meta univBCid.meta ⟩
      pure (value, .imax univA univB)
    | .param name => do
      let lvls := (← read).univCtx
      match lvls.indexOf? name with
      | some n =>
        let value : Ipld.Both Ipld.Univ := ⟨ .var n, .var name ⟩
        pure (value, .var name n)
      | none   => throw $ .levelNotFound name lvls
    | .mvar .. => throw $ .unfilledLevelMetavariable l
  let cid ← addToStore $ .univ value
  pure (cid, univ)

/-- Defines an ordering for Lean universes -/
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
  `compileConstant` to do the actual compilation.
  -/
  partial def getCompiledConst (const : Lean.ConstantInfo) :
      CompileM $ ConstCid × ConstIdx := do
    let name := const.name
    let log  := (← read).log
    match (← get).cache.find? name with
    | some c => pure c
    | none   =>
      if log then
        IO.println s!"↡ Stacking {name}{const.formatAll}"
      let c ← compileConstant const
      if log then
        IO.println s!"↟ Popping  {name}"
      pure c

  /--
  Performs the compilation of Lean constants.

  For the `.defnInfo`, `.inductInfo`, `.ctorInfo` and `.recInfo`  cases, the
  side-effects are responsability of the auxiliary functions.

  For other cases, adds them to the cache, the store and the array of constants.
  -/
  partial def compileConstant : Lean.ConstantInfo → CompileM (ConstCid × ConstIdx)
  -- These cases add multiple constants at the same time
  | .defnInfo struct => withLevelsAndReset struct.levelParams $ compileDefinition struct
  | .inductInfo struct => withLevelsAndReset struct.levelParams $ compileInductive struct
  -- These cases are subsumed by the inductive case
  | .ctorInfo struct => do
    discard $ match ← getLeanConstant struct.induct with
      | .inductInfo ind => getCompiledConst (.inductInfo ind)
      | const => throw $ .invalidConstantKind const "inductive"
    getCompiledConst (.ctorInfo struct)
  | .recInfo struct => do
    discard $ match ← getLeanConstant struct.getInduct with
      | .inductInfo ind => getCompiledConst (.inductInfo ind)
      | const => throw $ .invalidConstantKind const "inductive"
    getCompiledConst (.recInfo struct)
  -- The rest adds the constants to the cache one by one
  | const => withLevelsAndReset const.levelParams do
    -- It is important to push first with some value so we don't lose the
    -- position of the constant in a recursive call
    let constIdx ← modifyGet fun stt =>
      (stt.consts.size, { stt with consts := stt.consts.push default })
    let values : Ipld.Both Ipld.Const × Const ← match const with
      | .axiomInfo struct =>
        let (typeCid, type) ← compileExpr struct.type
        let ax := {
          name := struct.name
          lvls := struct.levelParams
          type := type
          safe := not struct.isUnsafe }
        let value := ⟨ .axiom $ ax.toIpld typeCid, .axiom $ ax.toIpld typeCid ⟩
        pure (value, .axiom ax)
      | .thmInfo struct =>
        let (typeCid, type) ← compileExpr struct.type
        -- Theorems are never truly recursive, though they can use recursive schemes
        let (valueCid, value) ← compileExpr struct.value
        let thm := {
          name  := struct.name
          lvls  := struct.levelParams
          type  := type
          value := value }
        let value := ⟨.theorem $ thm.toIpld typeCid valueCid, .theorem $ thm.toIpld typeCid valueCid⟩
        pure (value, Const.theorem thm)
      | .opaqueInfo struct =>
        let (typeCid, type) ← compileExpr struct.type
        let (valueCid, value) ← withRecrs (RBMap.single struct.name (0, some 0, constIdx)) $ compileExpr struct.value
        let opaq := {
          name  := struct.name
          lvls  := struct.levelParams
          type  := type
          value := value
          safe  := not struct.isUnsafe }
          let value := ⟨.opaque $ opaq.toIpld typeCid valueCid, .opaque $ opaq.toIpld typeCid valueCid⟩
        pure (value, .opaque opaq)
      | .quotInfo struct =>
        let (typeCid, type) ← compileExpr struct.type
        let quot := {
          name := struct.name
          lvls := struct.levelParams
          type := type
          kind := struct.kind }
        let value := ⟨.quotient $ quot.toIpld typeCid, .quotient $ quot.toIpld typeCid⟩
        pure (value, .quotient quot)
      | _ => unreachable! -- the other cases were already dealt with
    let cid ← addToStore $ .const values.fst
    addToConsts constIdx values.snd
    addToCache const.name (cid, constIdx)
    pure (cid, constIdx)

  /--
  Compiles a Lean expression and adds it to the store.

  Constants are the tricky case, for which there are two possibilities:
  * The constant belongs to `recrCtx`, representing a recursive call. Those are
  encoded as variables with indexes that go beyond the bind indexes
  * The constant doesn't belong to `recrCtx`, meaning that it's not a recursion
  and thus we can compile the actual constant right away
  -/
  partial def compileExpr : Lean.Expr → CompileM (ExprCid × Expr)
  | .mdata _ e => compileExpr e
  | expr => do
    let (value, expr) ← match expr with
      | .bvar idx => match (← read).bindCtx.get? idx with
        -- Bound variables must be in the bind context
        | some name =>
          let value : Ipld.Both Ipld.Expr := ⟨ .var idx () [], .var name (Split.injᵣ none) [] ⟩
          pure (value, .var name idx)
        | none => throw $ .invalidBVarIndex idx
      | .sort lvl =>
        let (univCid, univ) ← compileUniv lvl
        let value : Ipld.Both Ipld.Expr := ⟨ .sort univCid.anon, .sort univCid.meta ⟩
        pure (value, .sort univ)
      | .const name lvls =>
        let pairs ← lvls.mapM $ compileUniv
        let (univCids, univs) ← pairs.foldrM (init := ([], []))
          fun pair pairs => pure (pair.fst :: pairs.fst, pair.snd :: pairs.snd)
        match (← read).recrCtx.find? name with
        | some (i, i?, ref) => -- recursing!
          let idx := (← read).bindCtx.length + i
          let value : Ipld.Both Ipld.Expr := ⟨ .var idx () (univCids.map (·.anon)),
            .var name i? (univCids.map (·.meta)) ⟩
          pure (value, .const name ref univs)
        | none =>
          let const ← getLeanConstant name
          let (constCid, const) ← getCompiledConst const
          let value : Ipld.Both Ipld.Expr :=
            ⟨ .const () constCid.anon $ univCids.map (·.anon),
              .const name constCid.meta $ univCids.map (·.meta) ⟩
          pure (value, .const name const univs)
      | .app fnc arg =>
        let (fncCid, fnc) ← compileExpr fnc
        let (argCid, arg) ← compileExpr arg
        let value : Ipld.Both Ipld.Expr :=
          ⟨ .app fncCid.anon argCid.anon, .app fncCid.meta argCid.meta ⟩
        pure (value, .app fnc arg)
      | .lam name typ bod bnd =>
        let (typCid, typ) ← compileExpr typ
        let (bodCid, bod) ← withBinder name $ compileExpr bod
        let value : Ipld.Both Ipld.Expr :=
          ⟨ .lam () bnd typCid.anon bodCid.anon, .lam name () typCid.meta bodCid.meta ⟩
        pure (value, .lam name bnd typ bod)
      | .forallE name dom img bnd =>
        let (domCid, dom) ← compileExpr dom
        let (imgCid, img) ← withBinder name $ compileExpr img
        let value : Ipld.Both Ipld.Expr :=
          ⟨ .pi () bnd domCid.anon imgCid.anon, .pi name () domCid.meta imgCid.meta ⟩
        pure (value, .pi name bnd dom img)
      | .letE name typ exp bod _ =>
        let (typCid, typ) ← compileExpr typ
        let (expCid, exp) ← compileExpr exp
        let (bodCid, bod) ← withBinder name $ compileExpr bod
        let value : Ipld.Both Ipld.Expr :=
          ⟨ .letE () typCid.anon expCid.anon bodCid.anon, .letE name typCid.meta expCid.meta bodCid.meta ⟩
        pure (value, .letE name typ exp bod)
      | .lit lit =>
        let value : Ipld.Both Ipld.Expr := ⟨ .lit lit, .lit () ⟩
        pure (value, .lit lit)
      | .proj _ idx exp =>
        let (expCid, exp) ← compileExpr exp
        let value : Ipld.Both Ipld.Expr := ⟨ .proj idx expCid.anon, .proj () expCid.meta ⟩
        pure (value, .proj idx exp)
      | .fvar ..  => throw $ .freeVariableExpr expr
      | .mvar ..  => throw $ .metaVariableExpr expr
      | .mdata .. => throw $ .metaDataExpr expr
    let cid ← addToStore $ .expr value
    pure (cid, expr)

  /--
  Compiles an inductive and all inductives in the mutual block as a mutual
  block, even if the inductive itself is not in a mutual block.

  The compilation of an inductive involves the compilation of its associated
  constructors and recursors, hence the lenght of this function.
  -/
  partial def compileInductive (initInd : Lean.InductiveVal) :
      CompileM (ConstCid × ConstIdx) := do
    -- `mutualConsts` is the list of the names of all constants associated with an
    -- inductive block: the inductives themselves, the constructors and the recursors
    let mut mutualConsts : List Lean.Name := []
    for indName in initInd.all do
      match ← getLeanConstant indName with
      | .inductInfo ind =>
        let leanRecs := ((← read).constMap.childrenOfWith ind.name
          fun c => match c with | .recInfo _ => true | _ => false).map (·.name)
        mutualConsts := mutualConsts ++ (indName :: ind.ctors) ++ leanRecs
      | const => throw $ .invalidConstantKind const "inductive"

    -- All inductives, constructors and recursors are done in one go, so we must
    -- append an array of `mutualConsts.length` to `consts` and save the mapping
    -- of all names in `mutualConsts` to their respective indices
    let mut firstIdx : ConstIdx ← modifyGet fun stt =>
      (stt.consts.size,
        { stt with consts := stt.consts ++ mkArray mutualConsts.length default })

    let recrCtx := mutualConsts.enum.foldl (init := default)
      fun acc (i, n) => acc.insert n (i, none, firstIdx + i)

    -- This part will build the inductive block and add all inductives,
    -- constructors and recursors to `consts`
    let ipldInds : List (Ipld.Both Ipld.Inductive) ← initInd.all.foldrM (init := [])
      fun name acc => do
        match ← getLeanConstant name with
        | .inductInfo ind => do
          withRecrs recrCtx do
            let ipldInd ← toYatimaIpldInductive ind
            pure $ ipldInd :: acc
        | const => throw $ .invalidConstantKind const "inductive"
    let indBlockCid ← addToStore $ .const
      ⟨.mutIndBlock $ ipldInds.map (·.anon), .mutIndBlock $ ipldInds.map (·.meta)⟩

    -- While iterating on the inductives from the mutual block, we need to track
    -- the correct objects to return
    let mut ret? : Option (ConstCid × ConstIdx) := none

    -- `constIdx` keeps track of the constant index for the next addition to cache
    let mut constIdx := firstIdx

    for (indIdx, ⟨indAnon, indMeta⟩) in ipldInds.enum do
      -- Store and cache inductive projections
      let name := indMeta.name.projᵣ
      let indProj :=
        ⟨ .inductiveProj ⟨ (), indAnon.lvls, indAnon.type, indBlockCid.anon, indIdx ⟩
        , .inductiveProj ⟨ indMeta.name, indMeta.lvls, indMeta.type, indBlockCid.meta, () ⟩ ⟩
      let cid ← addToStore $ .const indProj
      if name == initInd.name then ret? := some (cid, constIdx)
      addToCache name (cid, constIdx)
      constIdx := constIdx + 1

      for (ctorIdx, (ctorAnon, ctorMeta)) in (indAnon.ctors.zip indMeta.ctors).enum do
        -- Store and cache constructor projections
        let name := ctorMeta.name.projᵣ
        let ctorProj :=
          ⟨ .constructorProj ⟨ (), ctorAnon.lvls, ctorAnon.type, indBlockCid.anon, indIdx, ctorIdx ⟩
          , .constructorProj ⟨ ctorMeta.name, ctorMeta.lvls, ctorMeta.type, indBlockCid.meta, (), () ⟩ ⟩
        let cid ← addToStore $ .const ctorProj
        addToCache name (cid, constIdx)
        constIdx := constIdx + 1

      for (recrIdx, (recrAnon, recrMeta)) in (indAnon.recrs.zip indMeta.recrs).enum do
        -- Store and cache recursor projections
        let name := recrMeta.2.name.projᵣ
        let recrProj :=
          ⟨ .recursorProj ⟨ (), recrAnon.2.lvls, recrAnon.2.type, indBlockCid.anon, indIdx, recrIdx ⟩
          , .recursorProj ⟨ recrMeta.2.name, recrMeta.2.lvls, recrMeta.2.type, indBlockCid.meta, (), () ⟩ ⟩
        let cid ← addToStore $ .const recrProj
        addToCache name (cid, constIdx)
        constIdx := constIdx + 1

    match ret? with
    | some ret => return ret
    | none => throw $ .constantNotCompiled initInd.name

  /-- Encodes a Lean inductive to IPLD -/
  partial def toYatimaIpldInductive (ind : Lean.InductiveVal) :
      CompileM $ Ipld.Both Ipld.Inductive := do
    let leanRecs := (← read).constMap.childrenOfWith ind.name
      fun c => match c with | .recInfo _ => true | _ => false
    let (recs, ctors) : (List $ Ipld.Both (Sigma fun x => Ipld.Recursor x ·)) ×
        (List $ Ipld.Both Ipld.Constructor) :=
      ← leanRecs.foldrM (init := ([], [])) fun r (recs, ctors) => do
        match r with
        | .recInfo rv =>
          if isInternalRec rv.type ind.name then
            let (thisRec, thisCtors) := ← toYatimaIpldInternalRec ind.ctors r
            let recs := ⟨Sigma.mk .intr thisRec.anon, Sigma.mk .intr thisRec.meta⟩ :: recs
            return (recs, thisCtors)
          else
            let thisRec ← toYatimaIpldExternalRec r
            let recs := ⟨Sigma.mk .extr thisRec.anon, Sigma.mk .extr thisRec.meta⟩ :: recs
            return (recs, ctors)
        | _ => throw $ .nonRecursorExtractedFromChildren r.name
    let (typeCid, type) ← compileExpr ind.type
    -- Structures can't be recursive nor have indices
    let struct ← if ind.isRec || ind.numIndices != 0 then pure none else
      match ind.ctors with
      -- Structures can only have one constructor
      | [ctorName] => do
        let (_, _, ctorIdx) ← getFromRecrCtx! ctorName
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
    let (_, _, constIdx) ← getFromRecrCtx! ind.name
    addToConsts constIdx tcInd
    return {
      anon := ⟨ ()
        , ind.levelParams.length
        , typeCid.anon
        , ind.numParams
        , ind.numIndices
        -- NOTE: for the purpose of conversion, the order of `ctors` and `recs` MUST match the order used in `recrCtx`
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

  /-- Encodes an internal recursor to to IPLD -/
  partial def toYatimaIpldInternalRec (ctors : List Lean.Name) :
    Lean.ConstantInfo → CompileM
      (Ipld.Both (Ipld.Recursor .intr) × (List $ Ipld.Both Ipld.Constructor))
    | .recInfo rec => do
      withLevels rec.levelParams do
        let (typeCid, type) ← compileExpr rec.type
        let ctorMap : RBMap Name (Ipld.Both Ipld.Constructor) compare ← rec.rules.foldlM
          (init := .empty) fun ctorMap r => do
            if ctors.contains r.ctor then
              let ctor ← toYatimaIpldConstructor r
              return ctorMap.insert ctor.meta.name.projᵣ ctor
            -- this is an external recursor rule
            else return ctorMap
        let retCtors ← ctors.mapM fun ctorName => do
          match ctorMap.find? ctorName with
          | some thisCtor => pure thisCtor
          | none => throw $ .custom s!"Couldn't find constructor {ctorName}"
        let tcRecr : Const := .intRecursor {
          name    := rec.name
          lvls    := rec.levelParams
          type    := type
          params  := rec.numParams
          indices := rec.numIndices
          motives := rec.numMotives
          minors  := rec.numMinors
          k       := rec.k }
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

  /-- Encodes a Lean constructor to IPLD -/
  partial def toYatimaIpldConstructor (rule : Lean.RecursorRule) :
      CompileM $ Ipld.Both Ipld.Constructor := do
    let (rhsCid, rhs) ← compileExpr rule.rhs
    match ← getLeanConstant rule.ctor with
    | .ctorInfo ctor =>
      withLevels ctor.levelParams do
      let (typeCid, type) ← compileExpr ctor.type
      let tcCtor : Const := .constructor {
        name    := ctor.name
        lvls    := ctor.levelParams
        type    := type
        idx     := ctor.cidx
        params  := ctor.numParams
        fields  := ctor.numFields
        -- the rhs of constructors are represented as implicit lambdas for an
        -- optimization in the typechecker
        rhs     := rhs.toImplicitLambda
        safe    := not ctor.isUnsafe
      }
      let (_, _, constIdx) ← getFromRecrCtx! ctor.name
      addToConsts constIdx tcCtor
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

  /-- Encodes an external recursor to IPLD -/
  partial def toYatimaIpldExternalRec :
      Lean.ConstantInfo → CompileM (Ipld.Both (Ipld.Recursor .extr))
    | .recInfo rec => withLevels rec.levelParams do
      let (typeCid, type) ← compileExpr rec.type
      let (rules, tcRules) : Ipld.Both (fun k => List $ Ipld.RecursorRule k) × List RecursorRule := ← rec.rules.foldlM
        (init := (⟨[], []⟩, [])) fun rules r => do
          let (recrRule, tcRecrRule) ← toYatimaIpldExternalRecRule r
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

  /-- Encodes an external recursor rule to IPLD -/
  partial def toYatimaIpldExternalRecRule (rule : Lean.RecursorRule) :
      CompileM (Ipld.Both Ipld.RecursorRule × RecursorRule) := do
    let (rhsCid, rhs) ← compileExpr rule.rhs
    let const ← getLeanConstant rule.ctor
    let (ctorCid, ctor?) ← getCompiledConst const
    let ctor ← match ← derefConst ctor? with
      | .constructor ctor => pure ctor
      | const => throw $ .invalidConstantKind' const "constructor"
    let recrRule := ⟨
      { ctor := ctorCid.anon, fields := rule.nfields, rhs := rhsCid.anon },
      { ctor := ctorCid.meta, fields := (), rhs := rhsCid.meta }⟩
    let tcRecrRule := { ctor := ctor, fields := rule.nfields, rhs := rhs }
    return (recrRule, tcRecrRule)

  /--
  Compiles adefinition and all definitions in the mutual block as a mutual
  block, even if the definition itself is not in a mutual block.

  This function is rather similar to `Yatima.Compiler.compileInductive`.
  -/
  partial def compileDefinition (struct : Lean.DefinitionVal) :
      CompileM (ConstCid × ConstIdx) := do
    let mutualSize := struct.all.length

    -- This solves an issue in which the constant name comes different in the
    -- `all` attribute
    let all := if mutualSize == 1 then [struct.name] else struct.all

    -- Collecting and sorting all definitions in the mutual block
    let mutualDefs ← all.mapM fun name => do
      match ← getLeanConstant name with
      | .defnInfo defn => pure defn
      | const => throw $ .invalidConstantKind const "definition"
    let mutualDefs ← sortDefs [mutualDefs]
    
    -- Reserving the slots in the array of constants
    let mut firstIdx ← modifyGet fun stt =>
      (stt.consts.size, { stt with consts := stt.consts ++ mkArray mutualSize default })

    -- Building the `recrCtx`
    let mut recrCtx : RBMap Name RecrCtxEntry compare := RBMap.empty
    let mut mutIdx := 0
    for (i, ds) in mutualDefs.enum do
      for (j, d) in ds.enum do
        recrCtx := recrCtx.insert d.name (i, some j, firstIdx + mutIdx)
        mutIdx := mutIdx + 1

    let definitions ← withRecrs recrCtx $ mutualDefs.mapM (·.mapM toYatimaIpldDefinition)

    -- Building and storing the block
    let definitionsAnon := (definitions.map fun ds => match ds.head? with | some d => [d.1.anon] | none => []).join
    let definitionsMeta := definitions.map fun ds => ds.map $ (·.meta) ∘ Prod.fst
    let block : Ipld.Both Ipld.Const := ⟨ .mutDefBlock definitionsAnon, .mutDefBlock definitionsMeta ⟩
    let blockCid ← addToStore $ .const block

    -- While iterating on the definitions from the mutual block, we need to track
    -- the correct objects to return
    let mut ret? : Option (ConstCid × ConstIdx) := none

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
    | none => throw $ .constantNotCompiled struct.name

  /-- Encodes a definition to IPLD -/
  partial def toYatimaIpldDefinition (defn : Lean.DefinitionVal) :
      CompileM (Ipld.Both Ipld.Definition × Definition) := do
    let (typeCid, type) ← compileExpr defn.type
    let (valueCid, value) ← compileExpr defn.value
    let defn := {
      name   := defn.name
      lvls   := defn.levelParams
      type
      value
      safety := defn.safety }
    return (⟨defn.toIpld typeCid valueCid, defn.toIpld typeCid valueCid⟩, defn)

  /--
  A name-irrelevant ordering of Lean expressions. 
  `weakOrd` contains the best known current mutual ordering
  -/
  partial def cmpExpr (weakOrd : Std.RBMap Name Nat compare) :
      Lean.Expr → Lean.Expr → CompileM Ordering
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
        let xCid := (← getCompiledConst (← getLeanConstant x)).fst
        let yCid := (← getCompiledConst (← getLeanConstant y)).fst
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
      CompileM Ordering := do
    let ls := compare x.levelParams.length y.levelParams.length
    let ts ← cmpExpr weakOrd x.type y.type
    let vs ← cmpExpr weakOrd x.value y.value
    return concatOrds [ls, ts, vs]

  /-- AST equality between two Lean definitions.
    `weakOrd` contains the best known current mutual ordering -/
  partial def eqDef (weakOrd : Std.RBMap Name Nat compare)
      (x : Lean.DefinitionVal) (y : Lean.DefinitionVal) : CompileM Bool := do
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
      CompileM (List (List Lean.DefinitionVal)) := do
    let enum (ll : List (List Lean.DefinitionVal)) :=
      Std.RBMap.ofList (ll.enum.map fun (n, xs) => xs.map (·.name, n)).join
    let weakOrd := enum dss
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

/--
Iterates over the constants of a `Lean.ConstMap` triggering their compilation.

Once finished, tries to replace some operations by their primitive versions in
the array of constants.
-/
def compileM (constMap : Lean.ConstMap) : CompileM Unit := do
  match buildPrimOpMap with
  | .ok primOpMap =>
    let log := (← read).log
    constMap.forM fun _ const => do
      let (_, c) ← getCompiledConst const
      if log then
        IO.println "\n========================================="
        IO.println    const.name
        IO.println   "========================================="
        IO.println $  PrintLean.printLeanConst const
        IO.println   "========================================="
        IO.println $ ← PrintYatima.printYatimaConst (← derefConst c)
        IO.println   "=========================================\n"
    (← get).cache.forM fun _ c => do
      match primOpMap.find? c.1.anon with
      | some const => addToConsts c.2 const
      | none => pure ()
  | .error s => throw $ .custom s

/--
Compiles the "delta" of a file, that is, the content that is added on top of
what is imported by it.

Important: constants with open references in their expressions are filtered out.
Open references are variables that point to names which aren't present in the
`Lean.ConstMap`.
-/
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
Sets the directories where `olean` files can be found.

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
