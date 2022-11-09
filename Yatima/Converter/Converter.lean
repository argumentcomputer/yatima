import Yatima.Datatypes.Store
import YatimaStdLib.RBMap
import Yatima.Converter.ConvertError
import Yatima.Converter.ConvertM
import Yatima.Lurk.PrimConsts

namespace Yatima

namespace Converter

/-- Represents information used to retrieve data from the cache or from store -/
inductive Key : Type → Type
  | univCache  : IR.BothUnivScalar  → Key TC.Univ
  | constCache : IR.BothConstScalar → Key TC.ConstIdx
  | univStore  : IR.BothUnivScalar  → Key (IR.Both IR.Univ)
  | exprStore  : IR.BothExprScalar  → Key (IR.Both IR.Expr)
  | constStore : IR.BothConstScalar → Key (IR.Both IR.Const)

namespace Key

/-- Tries to retrieve data from the cache or store given a `Key` -/
def find? : (key : Key A) → ConvertM (Option A)
  | univCache  univ  => return (← get).univCache.find? univ
  | constCache const => return (← get).constCache.find? const
  | univStore  univ  => do
    let store := (← read).store
    let anon? := store.univAnon.find? univ.anon
    let meta? := store.univMeta.find? univ.meta
    match anon?, meta? with
    | some anon, some meta => pure $ some ⟨anon, meta⟩
    | _, _ => pure none
  | exprStore  expr  => do
    let store := (← read).store
    let anon? := store.exprAnon.find? expr.anon
    let meta? := store.exprMeta.find? expr.meta
    match anon?, meta? with
    | some anon, some meta => pure $ some ⟨anon, meta⟩
    | _, _ => pure none
  | constStore const => do
    let store := (← read).store
    let anon? := store.constAnon.find? const.anon
    let meta? := store.constMeta.find? const.meta
    match anon?, meta? with
    | some anon, some meta => pure $ some ⟨anon, meta⟩
    | _, _ => pure none

/--
Retrieves data from the cache or store with a key, raising an error if it's not
found
-/
def find (key : Key A) : ConvertM A := do
  ConvertM.unwrap (← find? key)

/-- Adds data to cache -/
def cache : (Key A) → A → ConvertM Unit
  | univCache  univ,  a => modify fun stt =>
    { stt with univCache  := stt.univCache.insert  univ  a }
  | constCache const, a => modify fun stt =>
    { stt with constCache := stt.constCache.insert const a }
  | _, _ => throw .cannotStoreValue

end Key

/-- Retrieves an inductive from a mutual block by its index -/
def getInductive : IR.Both IR.Const → Nat → ConvertM (IR.Both IR.Inductive)
  | ⟨.mutIndBlock indsAnon, .mutIndBlock indsMeta⟩, idx =>
    if h : idx < indsAnon.length ∧ idx < indsMeta.length then
      pure ⟨indsAnon[idx]'(h.1), indsMeta[idx]'(h.2)⟩
    else throw .irError
  | _, _ => throw .irError

/-- Retrieves a definition from a mutual block by its index -/
def getDefinition : IR.Both IR.Const → Nat → ConvertM (IR.Both IR.Definition)
  | ⟨.mutDefBlock defsAnon, .mutDefBlock defsMeta⟩, idx => do
    let defsMeta' := (defsMeta.map (·.projᵣ)).join
    let defsAnon' := (← defsMeta.enum.mapM fun (i, defMeta) =>
      if h : i < defsAnon.length then
        return List.replicate defMeta.projᵣ.length (defsAnon[i]'h).projₗ
      else throw .irError).join
    match defsAnon'.get? idx, defsMeta'.get? idx with
    | some defAnon, some defMeta => pure ⟨defAnon, defMeta⟩
    | _,            _            => throw .irError
  | _, _ => throw .irError

/-- Applies a function to each element of the list in `IR.Both (List $ A ·)` -/
def zipWith (f : IR.Both A → ConvertM B) :
    (as : IR.Both (List $ A ·)) → ConvertM (List B)
  | ⟨anon::anons, meta::metas⟩ => do
    let b  ← f ⟨anon, meta⟩
    let bs ← zipWith f ⟨anons, metas⟩
    pure $ b :: bs
  | ⟨[], []⟩ => pure []
  | _ => throw .irError

instance : Coe (Split A B .true)  A := ⟨Split.projₗ⟩
instance : Coe (Split A B .false) B := ⟨Split.projᵣ⟩

/-- Extracts an `Univ` from an `IR.BothUnivCid` -/
partial def univFromIR (cid : IR.BothUnivScalar) : ConvertM TC.Univ := do
  match ← Key.find? $ .univCache $ cid with
  | some univ => pure univ
  | none =>
    let ⟨anon, meta⟩ ← Key.find $ .univStore cid
    let univ ← match anon, meta with
      | .zero, .zero => pure .zero
      | .succ univAnon, .succ univMeta =>
        pure $ .succ (← univFromIR ⟨univAnon, univMeta⟩)
      | .max univAnon₁ univAnon₂, .max univMeta₁ univMeta₂ =>
        pure $ .max (← univFromIR ⟨univAnon₁, univMeta₁⟩)
          (← univFromIR ⟨univAnon₂, univMeta₂⟩)
      | .imax univAnon₁ univAnon₂, .imax univMeta₁ univMeta₂ =>
        pure $ .imax (← univFromIR ⟨univAnon₁, univMeta₁⟩)
          (← univFromIR ⟨univAnon₂, univMeta₂⟩)
      | .var idx, .var nam => pure $ .var nam idx
      | a, b => throw $ .anonMetaMismatch a.ctorName b.ctorName
    Key.cache (.univCache cid) univ
    pure univ

/-- Whether an inductive is an unit inductive or not -/
def inductiveIsUnit (ind : IR.Inductive .anon) : Bool :=
  if ind.recr || ind.indices.projₗ != 0 then false
  else match ind.ctors with
    | [ctor] => ctor.fields.projₗ == 0
    | _ => false

/-- Retrieves a constant index by its name -/
def getConstIdx (n : Name) : ConvertM Nat := do
  match (← get).constsIdx.find? n with
  | some idx => pure idx
  | none => throw $ .constIdxNotFound $ n.toString

/-- Builds the `RecrCtx` for mutual inductives -/
def getIndRecrCtx (indBlock : IR.Both IR.Const) : ConvertM RecrCtx := do
  let indBlockMeta ← match indBlock.meta with
    | .mutIndBlock x => pure x
    | _ => throw $ .invalidMutBlock indBlock.meta.ctorName
  let mut constList : List (Nat × Name) := []
  for ind in indBlockMeta do
    let indIdx ← getConstIdx ind.name.projᵣ
    let indTup := (indIdx, ind.name.projᵣ)
    let ctorTups : List (Nat × Name) ← ind.ctors.mapM fun ctor => do
      let name := ctor.name
      let indIdx ← getConstIdx name
      return (indIdx, name)
    let recTups : List (Nat × Name) ← ind.recrs.mapM fun ⟨_, recr⟩ => do
      let name := recr.name
      let indIdx ← getConstIdx name
      return (indIdx, name)
    -- mirror the compiler order of inductive, then constuctors, then recursors
    let addList := (indTup :: ctorTups).append recTups
    constList := constList.append addList
  return constList.enum.foldl (init := default)
    fun acc (i, tup) => acc.insert (i, none) tup

mutual

  /--
  Extracts the structure (constructor) from an inductive if it is a structure-like
  inductive, returns `none` otherwise.
  -/
  partial def getStructure (ind : IR.Both IR.Inductive) :
      ConvertM (Option TC.Constructor) :=
    if ind.anon.recr || ind.anon.indices.projₗ != 0 then pure $ none
    else match ind.anon.ctors, ind.meta.ctors with
      | [ctorAnon], [ctorMeta] => do
        pure $ some (← ctorFromIR ⟨ctorAnon, ctorMeta⟩)
      | _, _ => pure none

  /--
  Extracts an `Expr` given a `IR.BothExprScalar` representing an expression with
  the caveat that the `.var` case may represent a recursive reference.
  -/
  partial def exprFromIR (cid : IR.BothExprScalar) : ConvertM TC.Expr := do
    match ← Key.find $ .exprStore cid with
    | ⟨.var idx () lvlsAnon, .var name idx' lvlsMeta⟩ =>
      let depth := (← read).bindDepth
      if depth > idx.projₗ then
        -- this is a bound free variable
        if !lvlsAnon.isEmpty then
          -- bound free variables should never have universe levels
          throw $ .invalidIndexDepth idx.projₗ depth
        pure $ .var default name.projᵣ idx
      else
        -- this free variable came from recrCtx, and thus represents a mutual reference
        let lvls ← lvlsAnon.zip lvlsMeta |>.mapM
          fun (anon, meta) => univFromIR ⟨anon, meta⟩
        match (← read).recrCtx.find? (idx.projₗ - depth, idx') with
        | some (constIdx, name) => pure $ .const default name constIdx lvls
        | none => throw $ .mutRefFVNotFound (idx.projₗ - depth)
    | ⟨.sort uAnonCid, .sort uMetaCid⟩ =>
      pure $ .sort default (← univFromIR ⟨uAnonCid, uMetaCid⟩)
    | ⟨.const () cAnonCid uAnonCids, .const name cMetaCid uMetaCids⟩ =>
      let const ← constFromIR ⟨cAnonCid, cMetaCid⟩
      let univs ← zipWith univFromIR ⟨uAnonCids, uMetaCids⟩
      pure $ .const default name const univs
    | ⟨.app fncAnon argAnon, .app fncMeta argMeta⟩ =>
      let fnc ← exprFromIR ⟨fncAnon, fncMeta⟩
      let arg ← exprFromIR ⟨argAnon, argMeta⟩
      pure $ .app default fnc arg
    | ⟨.lam () binfo domAnon bodAnon, .lam name () domMeta bodMeta⟩ =>
      let dom ← exprFromIR ⟨domAnon, domMeta⟩
      withNewBind do
        let bod ← exprFromIR ⟨bodAnon, bodMeta⟩
        pure $ .lam default name binfo dom bod
    | ⟨.pi () binfo domAnon codAnon, .pi name () domMeta codMeta⟩ =>
      let dom ← exprFromIR ⟨domAnon, domMeta⟩
      withNewBind do
        let cod ← exprFromIR ⟨codAnon, codMeta⟩
        pure $ .pi default name binfo dom cod
    | ⟨.letE () typAnon valAnon bodAnon, .letE name typMeta valMeta bodMeta⟩ =>
      let typ ← exprFromIR ⟨typAnon, typMeta⟩
      let val ← exprFromIR ⟨valAnon, valMeta⟩
      withNewBind do
        let bod ← exprFromIR ⟨bodAnon, bodMeta⟩
        pure $ .letE default name typ val bod
    | ⟨.lit lit, .lit ()⟩ => pure $ .lit default lit
    | ⟨.proj idx bodAnon, .proj () bodMeta⟩ =>
      let bod ← exprFromIR ⟨bodAnon, bodMeta⟩
      pure $ .proj default idx bod
    | ⟨a, b⟩ => throw $ .anonMetaMismatch a.ctorName b.ctorName

  /-- Converts a `IR.BothConstCid` and return its constant index -/
  partial def constFromIR (cid : IR.BothConstScalar) :
      ConvertM TC.ConstIdx := do
    match ← Key.find? (.constCache cid) with
    | some constIdx => pure constIdx
    | none =>
      withResetBindDepth do
        let ⟨anon, meta⟩ := ← Key.find $ .constStore cid
        let some constIdx := (← get).constsIdx.find? meta.name
          | throw $ .cannotFindNameIdx $ toString meta.name
        let const ← match anon, meta with
        | .axiom axiomAnon, .axiom axiomMeta =>
          let name := axiomMeta.name
          let lvls := axiomMeta.lvls
          let type ← exprFromIR ⟨axiomAnon.type, axiomMeta.type⟩
          let safe := axiomAnon.safe
          pure $ .axiom { name, lvls, type, safe }
        | .theorem theoremAnon, .theorem theoremMeta =>
          let name := theoremMeta.name
          let lvls := theoremMeta.lvls
          let type ← exprFromIR ⟨theoremAnon.type, theoremMeta.type⟩
          let value ← exprFromIR ⟨theoremAnon.value, theoremMeta.value⟩
          pure $ .theorem { name, lvls, type, value }
        | .inductiveProj anon, .inductiveProj meta =>
          let indBlock ← Key.find $ .constStore ⟨anon.block, meta.block⟩
          let induct ← getInductive indBlock anon.idx
          let name := induct.meta.name
          let lvls := induct.meta.lvls
          let type ← exprFromIR ⟨induct.anon.type, induct.meta.type⟩
          let params := induct.anon.params
          let indices := induct.anon.indices
          let recr := induct.anon.recr
          let safe := induct.anon.safe
          let refl := induct.anon.refl
          let unit := inductiveIsUnit induct.anon

          let recrCtx ← getIndRecrCtx indBlock
          -- TODO optimize
          withRecrs recrCtx do
            -- if this is a structure, the `struct` field will reference the inductive, hence the need for `recrCtx`
            let struct ← getStructure induct
            pure $ .inductive { name, lvls, type, params, indices, recr, safe, refl, unit, struct }
        | .opaque opaqueAnon, .opaque opaqueMeta =>
          let name := opaqueMeta.name
          let lvls := opaqueMeta.lvls
          let type ← exprFromIR ⟨opaqueAnon.type, opaqueMeta.type⟩
          let value ← exprFromIR ⟨opaqueAnon.value, opaqueMeta.value⟩
          let safe := opaqueAnon.safe
          pure $ .opaque { name, lvls, type, value, safe }
        | .definitionProj definitionAnon, .definitionProj definitionMeta =>
          let defn ← getDefinition (← Key.find $ .constStore ⟨definitionAnon.block, definitionMeta.block⟩) definitionMeta.idx
          match ← Key.find $ .constStore ⟨definitionAnon.block, definitionMeta.block⟩ with
          | ⟨.mutDefBlock _, .mutDefBlock metas⟩ =>
            let metas := metas.map (·.projᵣ)
            let name := defn.meta.name
            let lvls := defn.meta.lvls
            let safety := defn.anon.safety
            let mut recrCtx : RecrCtx := default
            for (i, ms) in metas.enum do
              for (j, m) in ms.enum do
                recrCtx := recrCtx.insert (i, some j) (← getConstIdx m.name, m.name)
            let type ← exprFromIR ⟨defn.anon.type, defn.meta.type⟩
            let all := recrCtx.toList.map fun (_, x, _) => x
            withRecrs recrCtx do
              let value ← exprFromIR ⟨defn.anon.value, defn.meta.value⟩
              pure $ .definition { name, lvls, type, value, safety, all }
          | _ => throw $ .unexpectedConst meta.ctorName "mutDefBlock"
        | .constructorProj anon, .constructorProj meta =>
          let indBlock ← Key.find $ .constStore ⟨anon.block, meta.block⟩
          let induct ← getInductive indBlock anon.idx
          let constructorAnon ← ConvertM.unwrap $ induct.anon.ctors.get? anon.cidx
          let constructorMeta ← ConvertM.unwrap $ induct.meta.ctors.get? anon.cidx
          let name   := constructorMeta.name
          let lvls   := constructorMeta.lvls
          let idx    := constructorAnon.idx
          let params := constructorAnon.params
          let fields := constructorAnon.fields
          let safe   := constructorAnon.safe

          let recrCtx ← getIndRecrCtx indBlock
          -- TODO optimize
          withRecrs recrCtx do
            let type ← exprFromIR ⟨constructorAnon.type, constructorMeta.type⟩
            let rhs ← exprFromIR ⟨constructorAnon.rhs, constructorMeta.rhs⟩
            pure $ .constructor { name, lvls, type, idx, params, fields, rhs, safe }
        | .recursorProj anon, .recursorProj meta =>
          let indBlock ← Key.find $ .constStore ⟨anon.block, meta.block⟩
          let induct ← getInductive indBlock anon.idx
          let pairAnon ← ConvertM.unwrap $ induct.anon.recrs.get? anon.ridx
          let pairMeta ← ConvertM.unwrap $ induct.meta.recrs.get? anon.ridx
          let recursorAnon := Sigma.snd pairAnon
          let recursorMeta := Sigma.snd pairMeta
          let name := recursorMeta.name
          let lvls := recursorMeta.lvls
          let params := recursorAnon.params
          let indices := recursorAnon.indices
          let motives := recursorAnon.motives
          let minors := recursorAnon.minors
          let k := recursorAnon.k

          let recrCtx ← getIndRecrCtx indBlock
          -- TODO optimize
          withRecrs recrCtx do
            let type ← exprFromIR ⟨recursorAnon.type, recursorMeta.type⟩
            let casesExtInt : (t₁ : IR.RecType) → (t₂ : IR.RecType) →
              (IR.Recursor t₁ .anon) → (IR.Recursor t₂ .meta) → ConvertM TC.Const
            | .intr, .intr, _, _ => pure $ .intRecursor { name, lvls, type, params, indices, motives, minors, k }
            | .extr, .extr, recAnon, recMeta => do
              let rules ← zipWith ruleFromIR ⟨recAnon.rules, recMeta.rules⟩
              pure $ .extRecursor { name, lvls, type, params, indices, motives, minors, rules, k }
            | _, _, _, _ => throw .irError
            casesExtInt (Sigma.fst pairAnon) (Sigma.fst pairMeta) recursorAnon recursorMeta
        | .quotient quotientAnon, .quotient quotientMeta =>
          let name := quotientMeta.name
          let lvls := quotientMeta.lvls
          let type ← exprFromIR ⟨quotientAnon.type, quotientMeta.type⟩
          let kind := quotientAnon.kind
          pure $ .quotient { name, lvls, type, kind }
        | .mutDefBlock .., .mutDefBlock .. => throw .mutDefBlockFound
        | .mutIndBlock .., .mutIndBlock .. => throw .mutIndBlockFound
        | a, b => throw $ .anonMetaMismatch a.ctorName b.ctorName
        Key.cache (.constCache cid) constIdx
        let tcStore := (← get).tcStore
        let consts := tcStore.consts
        let maxSize := consts.size
        if h : constIdx < maxSize then
          set { ← get with tcStore := { tcStore with consts := consts.set ⟨constIdx, h⟩ const } }
        else
          throw $ .constIdxOutOfRange constIdx maxSize
        pure constIdx

  /-- Converts a `IR.Both IR.Constructor` into a `Constructor` -/
  partial def ctorFromIR (ctor : IR.Both IR.Constructor) :
      ConvertM TC.Constructor := do
    let name := ctor.meta.name
    let lvls := ctor.meta.lvls
    let type ← exprFromIR ⟨ctor.anon.type, ctor.meta.type⟩
    let rhs ← exprFromIR ⟨ctor.anon.rhs, ctor.meta.rhs⟩
    let idx := ctor.anon.idx
    let params := ctor.anon.params
    let fields := ctor.anon.fields
    let safe := ctor.anon.safe
    pure { name, lvls, type, idx, params, fields, rhs, safe }

  /-- Converts a `IR.Both IR.RecursorRule` into a `RecursorRule` -/
  partial def ruleFromIR (rule : IR.Both IR.RecursorRule) :
      ConvertM TC.RecursorRule := do
    let rhs ← exprFromIR ⟨rule.anon.rhs, rule.meta.rhs⟩
    let ctorIdx ← constFromIR ⟨rule.anon.ctor, rule.meta.ctor⟩
    let consts := (← get).tcStore.consts
    let maxSize := consts.size
    if h : ctorIdx < maxSize then
      let ctor ← match consts[ctorIdx]'h with
        | .constructor ctor => pure ctor
        | _ => throw .irError
      return { rhs, ctor, fields := rule.anon.fields }
    else
      throw $ .constIdxOutOfRange ctorIdx maxSize

end

/--
Creates an initial array of constants full of dummy values to be replaced and
then calls `constFromIR` for each constant to be converted from the store
-/
def convertStore (store : IR.Store) : Except ConvertError ConvertState :=
  ConvertM.run (ConvertEnv.init store) default do
    let relevantMetas := (← read).store.constMeta.toList.filter
      fun (_, a) => a.isNotMutBlock
    relevantMetas.enum.forM fun (idx, (_, meta)) => do
      modifyGet fun state => (default, { state with
        tcStore := { state.tcStore with consts := state.tcStore.consts.push default },
        constsIdx := state.constsIdx.insert meta.name idx })
    (← read).store.consts.forM fun cid => discard $ constFromIR cid
    (← get).constCache.forM fun cid idx => do
      match IR.primConstsMap.find? cid.anon.data with
      | some pc => modify fun stt => { stt with tcStore := { stt.tcStore with
        primIdxs := stt.tcStore.primIdxs.insert pc idx
        idxsToPrims := stt.tcStore.idxsToPrims.insert idx pc } }
      | none => pure ()

/--
Main function in the converter API. Extracts the final array of constants from
an `IR.Store`
-/
def extractPureStore (store : IR.Store) : Except String TC.Store :=
  match convertStore store with
  | .ok stt => pure stt.tcStore
  | .error err => .error $ toString err

end Converter

end Yatima
