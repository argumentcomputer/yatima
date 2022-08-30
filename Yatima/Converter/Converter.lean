import Yatima.Datatypes.Store
import YatimaStdLib.RBMap
import Yatima.Compiler.Utils
import Yatima.Converter.ConvertError
import Yatima.Converter.ConvertM

namespace Yatima

namespace Converter

/-- Represents information used to retrieve data from the cache or from store -/
inductive Key : Type → Type
  | univ_cache  : UnivCid  → Key Univ
  | const_cache : ConstCid → Key ConstIdx
  | univ_store  : UnivCid  → Key (Ipld.Both Ipld.Univ)
  | expr_store  : ExprCid  → Key (Ipld.Both Ipld.Expr)
  | const_store : ConstCid → Key (Ipld.Both Ipld.Const)

namespace Key

/-- Tries to retrieve data from the cache or store given a `Key` -/
def find? : (key : Key A) → ConvertM (Option A)
  | univ_cache  univ  => return (← get).univ_cache.find? univ
  | const_cache const => return (← get).const_cache.find? const
  | univ_store  univ  => do
    let store := (← read).store
    let anon? := store.univ_anon.find? univ.anon
    let meta? := store.univ_meta.find? univ.meta
    match anon?, meta? with
    | some anon, some meta => pure $ some ⟨anon, meta⟩
    | _, _ => pure none
  | expr_store  expr  => do
    let store := (← read).store
    let anon? := store.expr_anon.find? expr.anon
    let meta? := store.expr_meta.find? expr.meta
    match anon?, meta? with
    | some anon, some meta => pure $ some ⟨anon, meta⟩
    | _, _ => pure none
  | const_store const => do
    let store := (← read).store
    let anon? := store.const_anon.find? const.anon
    let meta? := store.const_meta.find? const.meta
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
  | univ_cache  univ,  a => modify fun stt =>
    { stt with univ_cache  := stt.univ_cache.insert  univ  a }
  | const_cache const, a => modify fun stt =>
    { stt with const_cache := stt.const_cache.insert const a }
  | _, _ => throw .cannotStoreValue

end Key

/-- Retrieves an inductive from a mutual block by its index -/
def getInductive : Ipld.Both Ipld.Const → Nat → ConvertM (Ipld.Both Ipld.Inductive)
  | ⟨.mutIndBlock indsAnon, .mutIndBlock indsMeta⟩, idx =>
    if h : idx < indsAnon.length ∧ idx < indsMeta.length then
      pure ⟨indsAnon[idx]'(h.1), indsMeta[idx]'(h.2)⟩
    else throw .ipldError
  | _, _ => throw .ipldError

/-- Retrieves a definition from a mutual block by its index -/
def getDefinition : Ipld.Both Ipld.Const → Nat → ConvertM (Ipld.Both Ipld.Definition)
  | ⟨.mutDefBlock defsAnon, .mutDefBlock defsMeta⟩, idx => do
    let defsMeta' := (defsMeta.map (·.projᵣ)).join
    let defsAnon' := (← defsMeta.enum.mapM fun (i, defMeta) =>
      if h : i < defsAnon.length then
        return List.replicate defMeta.projᵣ.length (defsAnon[i]'h).projₗ
      else throw .ipldError).join
    match defsAnon'.get? idx, defsMeta'.get? idx with
    | some defAnon, some defMeta => pure ⟨defAnon, defMeta⟩
    | _,            _            => throw .ipldError
  | _, _ => throw .ipldError

/-- Applies a function to each element of the list in `Ipld.Both (List $ A ·)` -/
def Ipld.zipWith (f : Ipld.Both A → ConvertM B) :
    (as : Ipld.Both (List $ A ·)) → ConvertM (List B)
  | ⟨anon::anons, meta::metas⟩ => do
    let b  ← f ⟨anon, meta⟩
    let bs ← Ipld.zipWith f ⟨anons, metas⟩
    pure $ b :: bs
  | ⟨[], []⟩ => pure []
  | _ => throw .ipldError

instance : Coe (Split A B .true)  A := ⟨Split.projₗ⟩
instance : Coe (Split A B .false) B := ⟨Split.projᵣ⟩

/-- Extracts an `Univ` from an `UnivCid` -/
partial def univFromIpld (cid : UnivCid) : ConvertM Univ := do
  match ← Key.find? $ .univ_cache $ cid with
  | some univ => pure univ
  | none =>
    let ⟨anon, meta⟩ ← Key.find $ .univ_store cid
    let univ ← match anon, meta with
      | .zero, .zero => pure .zero
      | .succ univAnon, .succ univMeta =>
        pure $ .succ (← univFromIpld ⟨univAnon, univMeta⟩)
      | .max univAnon₁ univAnon₂, .max univMeta₁ univMeta₂ =>
        pure $ .max (← univFromIpld ⟨univAnon₁, univMeta₁⟩)
          (← univFromIpld ⟨univAnon₂, univMeta₂⟩)
      | .imax univAnon₁ univAnon₂, .imax univMeta₁ univMeta₂ =>
        pure $ .imax (← univFromIpld ⟨univAnon₁, univMeta₁⟩)
          (← univFromIpld ⟨univAnon₂, univMeta₂⟩)
      | .var idx, .var nam => pure $ .var nam idx
      | a, b => throw $ .anonMetaMismatch a.ctorName b.ctorName
    Key.cache (.univ_cache cid) univ
    pure univ

/-- Whether an inductive is an unit inductive or not -/
def inductiveIsUnit (ind : Ipld.Inductive .anon) : Bool :=
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
def getIndRecrCtx (indBlock : Ipld.Both Ipld.Const) : ConvertM RecrCtx := do
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

  /-- Extracts the structure (constructor) from an inductive if it is a structure-like
  inductive, returns `none` otherwise. -/
  partial def getStructure (ind : Ipld.Both Ipld.Inductive) :
      ConvertM (Option Constructor) :=
    if ind.anon.recr || ind.anon.indices.projₗ != 0 then pure $ none
    else match ind.anon.ctors, ind.meta.ctors with
      | [ctorAnon], [ctorMeta] => do
        pure $ some (← ctorFromIpld ⟨ctorAnon, ctorMeta⟩)
      | _, _ => pure none

  /--
  Extracts an `Expr` from IPLD CIDs representing an expression with the caveat
  that the `.var` case may represent a recursive reference.
  -/
  partial def exprFromIpld (cid : Ipld.Both Ipld.ExprCid) : ConvertM Expr := do
    match ← Key.find $ .expr_store cid with
    | ⟨.var idx () lvlsAnon, .var name idx' lvlsMeta⟩ =>
      let depth := (← read).bindDepth
      if depth > idx.projₗ then
        -- this is a bound free variable
        if !lvlsAnon.isEmpty then
          -- bound free variables should never have universe levels
          throw $ .invalidIndexDepth idx.projₗ depth
        return .var name.projᵣ idx
      else
        -- this free variable came from recrCtx, and thus represents a mutual reference
        let lvls ← lvlsAnon.zip lvlsMeta |>.mapM
          fun (anon, meta) => univFromIpld ⟨anon, meta⟩
        match (← read).recrCtx.find? (idx.projₗ - depth, idx') with
        | some (constIdx, name) => return .const name constIdx lvls
        | none => throw $ .mutRefFVNotFound (idx.projₗ - depth)
    | ⟨.sort uAnonCid, .sort uMetaCid⟩ =>
      pure $ .sort (← univFromIpld ⟨uAnonCid, uMetaCid⟩)
    | ⟨.const () cAnonCid uAnonCids, .const name cMetaCid uMetaCids⟩ =>
      let const ← constFromIpld ⟨cAnonCid, cMetaCid⟩
      let univs ← Ipld.zipWith univFromIpld ⟨uAnonCids, uMetaCids⟩
      pure $ .const name const univs
    | ⟨.app fncAnon argAnon, .app fncMeta argMeta⟩ =>
      let fnc ← exprFromIpld ⟨fncAnon, fncMeta⟩
      let arg ← exprFromIpld ⟨argAnon, argMeta⟩
      pure $ .app fnc arg
    | ⟨.lam () binfo domAnon bodAnon, .lam name () domMeta bodMeta⟩ =>
      let dom ← exprFromIpld ⟨domAnon, domMeta⟩
      withNewBind do
        let bod ← exprFromIpld ⟨bodAnon, bodMeta⟩
        pure $ .lam name binfo dom bod
    | ⟨.pi () binfo domAnon codAnon, .pi name () domMeta codMeta⟩ =>
      let dom ← exprFromIpld ⟨domAnon, domMeta⟩
      withNewBind do
        let cod ← exprFromIpld ⟨codAnon, codMeta⟩
        pure $ .pi name binfo dom cod
    | ⟨.letE () typAnon valAnon bodAnon, .letE name typMeta valMeta bodMeta⟩ =>
      let typ ← exprFromIpld ⟨typAnon, typMeta⟩
      let val ← exprFromIpld ⟨valAnon, valMeta⟩
      withNewBind do
        let bod ← exprFromIpld ⟨bodAnon, bodMeta⟩
        pure $ .letE name typ val bod
    | ⟨.lit lit, .lit ()⟩ => pure $ .lit lit
    | ⟨.proj idx bodAnon, .proj () bodMeta⟩ =>
      let bod ← exprFromIpld ⟨bodAnon, bodMeta⟩
      pure $ .proj idx bod
    | ⟨a, b⟩ => throw $ .anonMetaMismatch a.ctorName b.ctorName

  /-- Converts IPLD CIDs for a constant and return its constant index -/
  partial def constFromIpld (cid : Ipld.Both Ipld.ConstCid) :
      ConvertM ConstIdx := do
    match ← Key.find? (.const_cache cid) with
    | some constIdx => pure constIdx
    | none =>
      withResetBindDepth do
        let ⟨anon, meta⟩ := ← Key.find $ .const_store cid
        let some constIdx := (← get).constsIdx.find? meta.name
          | throw $ .cannotFindNameIdx $ toString meta.name
        let const ← match anon, meta with
        | .axiom axiomAnon, .axiom axiomMeta =>
          let name := axiomMeta.name
          let lvls := axiomMeta.lvls
          let type ← exprFromIpld ⟨axiomAnon.type, axiomMeta.type⟩
          let safe := axiomAnon.safe
          pure $ .axiom { name, lvls, type, safe }
        | .theorem theoremAnon, .theorem theoremMeta =>
          let name := theoremMeta.name
          let lvls := theoremMeta.lvls
          let type ← exprFromIpld ⟨theoremAnon.type, theoremMeta.type⟩
          let value ← exprFromIpld ⟨theoremAnon.value, theoremMeta.value⟩
          pure $ .theorem { name, lvls, type, value }
        | .inductiveProj anon, .inductiveProj meta =>
          let indBlock ← Key.find $ .const_store ⟨anon.block, meta.block⟩
          let induct ← getInductive indBlock anon.idx
          let name := induct.meta.name
          let lvls := induct.meta.lvls
          let type ← exprFromIpld ⟨induct.anon.type, induct.meta.type⟩
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
          let type ← exprFromIpld ⟨opaqueAnon.type, opaqueMeta.type⟩
          let value ← exprFromIpld ⟨opaqueAnon.value, opaqueMeta.value⟩
          let safe := opaqueAnon.safe
          pure $ .opaque { name, lvls, type, value, safe }
        | .definitionProj definitionAnon, .definitionProj definitionMeta =>
          let defn ← getDefinition (← Key.find $ .const_store ⟨definitionAnon.block, definitionMeta.block⟩) definitionMeta.idx
          match ← Key.find $ .const_store ⟨definitionAnon.block, definitionMeta.block⟩ with
          | ⟨.mutDefBlock _, .mutDefBlock metas⟩ =>
            let metas := metas.map (·.projᵣ)
            let name := defn.meta.name
            let lvls := defn.meta.lvls
            let safety := defn.anon.safety
            let mut recrCtx : RecrCtx := default
            for (i, ms) in metas.enum do
              for (j, m) in ms.enum do
                recrCtx := recrCtx.insert (i, some j) (← getConstIdx m.name, m.name)
            let type ← exprFromIpld ⟨defn.anon.type, defn.meta.type⟩
            withRecrs recrCtx do
              let value ← exprFromIpld ⟨defn.anon.value, defn.meta.value⟩
              pure $ .definition { name, lvls, type, value, safety }
          | _ => throw $ .unexpectedConst meta.ctorName "mutDefBlock"
        | .constructorProj anon, .constructorProj meta =>
          let indBlock ← Key.find $ .const_store ⟨anon.block, meta.block⟩
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
            let type ← exprFromIpld ⟨constructorAnon.type, constructorMeta.type⟩
            let rhs ← exprFromIpld ⟨constructorAnon.rhs, constructorMeta.rhs⟩
            let rhs := rhs.toImplicitLambda 
            pure $ .constructor { name, lvls, type, idx, params, fields, rhs, safe }
        | .recursorProj anon, .recursorProj meta =>
          let indBlock ← Key.find $ .const_store ⟨anon.block, meta.block⟩
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
            let type ← exprFromIpld ⟨recursorAnon.type, recursorMeta.type⟩
            let casesExtInt : (t₁ : RecType) → (t₂ : RecType) → (Ipld.Recursor t₁ .anon) → (Ipld.Recursor t₂ .meta) → ConvertM Const
            | .intr, .intr, _, _ => pure $ .intRecursor { name, lvls, type, params, indices, motives, minors, k }
            | .extr, .extr, recAnon, recMeta => do
              let rules ← Ipld.zipWith ruleFromIpld ⟨recAnon.rules, recMeta.rules⟩
              pure $ .extRecursor { name, lvls, type, params, indices, motives, minors, rules, k }
            | _, _, _, _ => throw .ipldError
            casesExtInt (Sigma.fst pairAnon) (Sigma.fst pairMeta) recursorAnon recursorMeta
        | .quotient quotientAnon, .quotient quotientMeta =>
          let name := quotientMeta.name
          let lvls := quotientMeta.lvls
          let type ← exprFromIpld ⟨quotientAnon.type, quotientMeta.type⟩
          let kind := quotientAnon.kind
          pure $ .quotient { name, lvls, type, kind }
        | .mutDefBlock .., .mutDefBlock .. => throw .mutDefBlockFound
        | .mutIndBlock .., .mutIndBlock .. => throw .mutIndBlockFound
        | a, b => throw $ .anonMetaMismatch a.ctorName b.ctorName
        Key.cache (.const_cache cid) constIdx
        let consts := (← get).consts
        let maxSize := consts.size
        if h : constIdx < maxSize then
          set { ← get with consts := consts.set ⟨constIdx, h⟩ const }
        else
          throw $ .constIdxOutOfRange constIdx maxSize
        pure constIdx

  /-- Converts constructor IPLD CIDs into a `Constructor` -/
  partial def ctorFromIpld (ctor : Ipld.Both Ipld.Constructor) : ConvertM Constructor := do
    let name := ctor.meta.name
    let lvls := ctor.meta.lvls
    let type ← exprFromIpld ⟨ctor.anon.type, ctor.meta.type⟩
    let rhs ← exprFromIpld ⟨ctor.anon.rhs, ctor.meta.rhs⟩
    let rhs := rhs.toImplicitLambda 
    let idx := ctor.anon.idx
    let params := ctor.anon.params
    let fields := ctor.anon.fields
    let safe := ctor.anon.safe
    pure { name, lvls, type, idx, params, fields, rhs, safe }

  /-- Converts recursor rule IPLD CIDs into a `RecursorRule` -/
  partial def ruleFromIpld (rule : Ipld.Both Ipld.RecursorRule) : ConvertM RecursorRule := do
    let rhs ← exprFromIpld ⟨rule.anon.rhs, rule.meta.rhs⟩
    let ctorIdx ← constFromIpld ⟨rule.anon.ctor, rule.meta.ctor⟩
    let consts := (← get).consts
    let maxSize := consts.size
    if h : ctorIdx < maxSize then
      let ctor ← match consts[ctorIdx]'h with
        | .constructor ctor => pure ctor
        | _ => throw .ipldError
      return { rhs, ctor, fields := rule.anon.fields }
    else
      throw $ .constIdxOutOfRange ctorIdx maxSize

end

/--
Creates an initial array of constants full of dummy values to be replaced and
then calls `constFromIpld` for each constant to be converted from the store
-/
def convertStore (store : Ipld.Store) : Except ConvertError ConvertState :=
  ConvertM.run (ConvertEnv.init store) default do
    (← read).store.const_meta.toList.enum.forM fun (idx, (_, meta)) => do
      modifyGet fun state => (default, { state with
        consts := state.consts.push default,
        constsIdx := state.constsIdx.insert meta.name idx })
    (← read).store.consts.forM fun cid => discard $ constFromIpld cid

/--
Main function in the converter API. Extracts the final array of constants from
an `Ipld.Store`
-/
def extractConstArray (store : Ipld.Store) : Except String (Array Const) :=
  match convertStore store with
  | .ok stt => pure stt.consts
  | .error err => .error $ toString err

end Converter

end Yatima
