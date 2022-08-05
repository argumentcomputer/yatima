import Yatima.Datatypes.Store
import Yatima.Compiler.Utils
import YatimaStdLib.RBMap

namespace Yatima

namespace FromIpld

open Std (RBMap)

-- Conversion monad
inductive ConvertError where
  | cannotFindAnon : ConvertError
  | cannotFindMeta : ConvertError
  | ipldError : ConvertError
  | cannotStoreValue : ConvertError
  | mutDefBlockFound : ConvertError
  | mutIndBlockFound : ConvertError
  | anonMetaMismatch : String → String → ConvertError
  | cannotFindNameIdx : String → ConvertError
  | constIdxOutOfRange : Nat → Nat → ConvertError
  | invalidIndexDepth : Nat → Nat → ConvertError
  | invalidMutIndBlock : String → ConvertError
  | defnsIdxNotFound : String → ConvertError
  | mutRefFVNotFound : Nat → ConvertError
  deriving Inhabited

instance : ToString ConvertError where toString
  | .cannotFindAnon => "Cannot find anon"
  | .cannotFindMeta => "Cannot find meta"
  | .anonMetaMismatch anon meta => s!"Anon/Meta mismatch: Anon is of kind {anon} but Meta is of kind {meta}"
  | .ipldError => "IPLD broken"
  | .cannotStoreValue => "Cannot store value"
  | .mutDefBlockFound => "Found a mutual definition block inside an expression"
  | .mutIndBlockFound => "Found a mutual inductive block inside an expression"
  | .cannotFindNameIdx name => s!"Cannot find index for '{name}'"
  | .constIdxOutOfRange i max => s!"Const index {i} out of range. Must be < {max}"
  | .invalidIndexDepth i min => s!"Invalid mutual referencing free variable index {i}. Must be ≥ {min}"
  | .invalidMutIndBlock type => s!"Invalid mutual block Ipld.Const reference, {type} found."
  | .defnsIdxNotFound name => s!"Could not find {name} in index of definitions."
  | .mutRefFVNotFound i => s!"Could not find index {i} in index of mutual referencing free variables."

structure ConvertEnv where
  store     : Ipld.Store
  recrCtx   : RBMap Nat (Nat × Name) compare
  bindDepth : Nat
  deriving Inhabited

def ConvertEnv.init (store : Ipld.Store) : ConvertEnv :=
  ⟨store, default, 0⟩

structure ConvertState where
  univ_cache  : RBMap UnivCid Univ compare
  expr_cache  : RBMap ExprCid Expr compare
  const_cache : RBMap ConstCid ConstIdx compare
  defns       : Array Const
  defnsIdx    : RBMap Name ConstIdx compare
  deriving Inhabited

abbrev ConvertM := ReaderT ConvertEnv <| EStateM ConvertError ConvertState

def ConvertM.run (env : ConvertEnv) (ste : ConvertState) (m : ConvertM α) :
    Except ConvertError ConvertState :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ stt  => .ok stt
  | .error e _ => .error e

def ConvertM.unwrap : Option A → ConvertM A :=
  Option.option (throw .ipldError) pure

def withResetRecrs : ConvertM α → ConvertM α :=
  withReader $ fun e => { e with recrCtx := default, bindDepth := 0 }

def withRecrs (recrCtx : RBMap Nat (Nat × Name) compare) :
    ConvertM α → ConvertM α :=
  withReader $ fun e => { e with recrCtx }

def withNewBind : ConvertM α → ConvertM α :=
  withReader $ fun e => { e with bindDepth := e.bindDepth + 1 }

-- Auxiliary definitions
inductive Key : Type → Type
  | univ_cache  : UnivCid  → Key Univ
  | expr_cache  : ExprCid  → Key Expr
  | const_cache : ConstCid → Key ConstIdx
  | univ_store  : UnivCid  → Key (Ipld.Both Ipld.Univ)
  | expr_store  : ExprCid  → Key (Ipld.Both Ipld.Expr)
  | const_store : ConstCid → Key (Ipld.Both Ipld.Const)

def Key.find? : (key : Key A) → ConvertM (Option A)
  | .univ_cache  univ  => return (← get).univ_cache.find? univ
  | .expr_cache  expr  => return (← get).expr_cache.find? expr
  | .const_cache const => return (← get).const_cache.find? const
  | .univ_store  univ  => do
    let store := (← read).store
    let anon? := store.univ_anon.find? univ.anon
    let meta? := store.univ_meta.find? univ.meta
    match anon?, meta? with
    | some anon, some meta => pure $ some ⟨anon, meta⟩
    | _, _ => pure none
  | .expr_store  expr  => do
    let store := (← read).store
    let anon? := store.expr_anon.find? expr.anon
    let meta? := store.expr_meta.find? expr.meta
    match anon?, meta? with
    | some anon, some meta => pure $ some ⟨anon, meta⟩
    | _, _ => pure none
  | .const_store const => do
    let store := (← read).store
    let anon? := store.const_anon.find? const.anon
    let meta? := store.const_meta.find? const.meta
    match anon?, meta? with
    | some anon, some meta => pure $ some ⟨anon, meta⟩
    | _, _ => pure none

def Key.find (key : Key A) : ConvertM A := do
  ConvertM.unwrap (← Key.find? key)

def Key.store : (Key A) → A → ConvertM Unit
  | .univ_cache  univ,  a => modify (fun stt => { stt with univ_cache  := stt.univ_cache.insert  univ  a })
  | .expr_cache  expr,  a => modify (fun stt => { stt with expr_cache  := stt.expr_cache.insert  expr  a })
  | .const_cache const, a => modify (fun stt => { stt with const_cache := stt.const_cache.insert const a })
  | _, _ => throw .cannotStoreValue

def getInductive : Ipld.Both Ipld.Const → Nat → ConvertM (Ipld.Both Ipld.Inductive)
  | ⟨.mutIndBlock indsAnon, .mutIndBlock indsMeta⟩, idx => pure ⟨indsAnon.get! idx, indsMeta.get! idx⟩
  | _, _ => throw .ipldError

def getDefinition : Ipld.Both Ipld.Const → Nat → ConvertM (Ipld.Both Ipld.Definition)
  | ⟨.mutDefBlock defsAnon, .mutDefBlock defsMeta⟩, idx => do
    let defsMeta' := (defsMeta.map (·.proj₂)).join
    let defsAnon' := (defsMeta.enum.map (fun (i, defMeta) => List.replicate defMeta.proj₂.length $ (defsAnon.get! i).proj₁)).join
    match defsAnon'.get? idx, defsMeta'.get? idx with
    | some defAnon, some defMeta => pure ⟨defAnon, defMeta⟩
    | _, _                       => throw .ipldError
  | _, _ => throw .ipldError

def Ipld.zipWith {A : Ipld.Kind → Type} (f : Ipld.Both A → ConvertM B): (as : Ipld.Both (List $ A ·)) → ConvertM (List B)
  | ⟨anon::anons, meta::metas⟩ => do
    let b  ← f ⟨anon, meta⟩
    let bs ← Ipld.zipWith f ⟨anons, metas⟩
    pure $ b :: bs
  | ⟨[], []⟩ => pure []
  | _ => throw .ipldError

instance : Coe (Split A B .true) A where coe  := Split.proj₁
instance : Coe (Split A B .false) B where coe := Split.proj₂

-- Conversion functions
partial def univFromIpld (cid : UnivCid) : ConvertM Univ := do
  match ← Key.find? $ .univ_cache $ cid with
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
      | .var () idx, .var nam () => pure $ .var nam idx
      | a, b => throw $ .anonMetaMismatch a.ctorName b.ctorName
    Key.store (.univ_cache cid) univ
    pure univ
  | some univ => pure univ

def inductiveIsUnit (ind : Ipld.Inductive .Anon) : Bool :=
  if ind.recr || ind.indices.proj₁ != 0 then false
  else match ind.ctors with
    | [ctor] => ctor.fields.proj₁ == 0
    | _ => false

def getDefnIdx (n : Name) : ConvertM Nat := do
  match (← get).defnsIdx.find? n with
  | some idx => pure idx
  | none => throw $ .defnsIdxNotFound $ n.toString

mutual
  partial def inductiveIsStructure (ind : Ipld.Both Ipld.Inductive) : ConvertM (Option Constructor) :=
    if ind.anon.recr || ind.anon.indices.proj₁ != 0 then pure $ none
    else match ind.anon.ctors, ind.meta.ctors with
      | [ctorAnon], [ctorMeta] => do
        pure $ some (← ctorFromIpld ⟨ctorAnon, ctorMeta⟩)
      | _, _ => pure none

  partial def exprFromIpld (cid : Ipld.Both Ipld.ExprCid) : ConvertM Expr := do
    match ← Key.find? (.expr_cache cid) with
    | some expr => pure expr
    | none =>
      let ⟨anon, meta⟩ ← Key.find $ .expr_store cid
      let expr ← match anon, meta with
        | .var () idx lvlsAnon, .var name () lvlsMeta =>
          let depth := (← read).bindDepth
          if depth > idx.proj₁ then
            -- this is a bound free variable
            if !lvlsAnon.isEmpty then
              -- bound free variables should never have universe levels
              throw $ .invalidIndexDepth idx.proj₁ depth
            return .var name.proj₂ idx
          else
            -- this free variable came from recrCtx, and thus represents a mutual reference
            let lvls ← lvlsAnon.zip lvlsMeta |>.mapM fun (anon, meta) => univFromIpld ⟨anon, meta⟩
            match (← read).recrCtx.find? (idx.proj₁ - depth) with
            | some (constIdx, name) => return .const name constIdx lvls
            | none => throw $ .mutRefFVNotFound (idx.proj₁ - depth)
        | .sort uAnonCid, .sort uMetaCid =>
          pure $ .sort (← univFromIpld ⟨uAnonCid, uMetaCid⟩)
        | .const () cAnonCid uAnonCids, .const name cMetaCid uMetaCids =>
          let const ← constFromIpld ⟨cAnonCid, cMetaCid⟩
          let univs ← Ipld.zipWith univFromIpld ⟨uAnonCids, uMetaCids⟩
          pure $ .const name const univs
        | .app fncAnon argAnon, .app fncMeta argMeta =>
          let fnc ← exprFromIpld ⟨fncAnon, fncMeta⟩
          let arg ← exprFromIpld ⟨argAnon, argMeta⟩
          pure $ .app fnc arg
        | .lam () binfo domAnon bodAnon, .lam name () domMeta bodMeta =>
          dbg_trace s!"NEW LAM BIND {name.proj₂}"
          withNewBind do
            let dom ← exprFromIpld ⟨domAnon, domMeta⟩
            let bod ← exprFromIpld ⟨bodAnon, bodMeta⟩
            dbg_trace s!"FINISHED BIND {name.proj₂}"
            pure $ .lam name binfo dom bod
        | .pi () binfo domAnon codAnon, .pi name () domMeta codMeta =>
          dbg_trace s!"NEW PI BIND {name.proj₂}"
          withNewBind do
            let dom ← exprFromIpld ⟨domAnon, domMeta⟩
            let cod ← exprFromIpld ⟨codAnon, codMeta⟩
            dbg_trace s!"FINISHED BIND {name.proj₂}"
            pure $ .pi name binfo dom cod
        | .letE () typAnon valAnon bodAnon, .letE name typMeta valMeta bodMeta =>
          dbg_trace s!"NEW LET BIND {name.proj₂}"
          withNewBind do
            let typ ← exprFromIpld ⟨typAnon, typMeta⟩
            let val ← exprFromIpld ⟨valAnon, valMeta⟩
            let bod ← exprFromIpld ⟨bodAnon, bodMeta⟩
            dbg_trace s!"FINISHED BIND {name.proj₂}"
            pure $ .letE name typ val bod
        | .lit lit, .lit () => pure $ .lit lit
        | .lty lty, .lty () => pure $ .lty lty
        | .proj idx bodAnon, .proj () bodMeta =>
          let bod ← exprFromIpld ⟨bodAnon, bodMeta⟩
          pure $ .proj idx bod
        | a, b => throw $ .anonMetaMismatch a.ctorName b.ctorName
      Key.store (.expr_cache cid) expr
      pure expr

  partial def constFromIpld (cid : Ipld.Both Ipld.ConstCid) :
      ConvertM ConstIdx := do
    match ← Key.find? (.const_cache cid) with
    | some constIdx =>
      dbg_trace s!"FOUND CACHED {(← get).defns[constIdx]!.name}"
      pure constIdx
    | none => withResetRecrs do
      let ⟨anon, meta⟩ := ← Key.find $ .const_store cid
      let some constIdx := (← get).defnsIdx.find? meta.name
        | throw $ .cannotFindNameIdx $ toString meta.name
      dbg_trace s!"------------PROCESSING {meta.name} ({meta.ctorName})"
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
        dbg_trace s!">> deserializing type of {name.proj₂}"
        let type ← exprFromIpld ⟨induct.anon.type, induct.meta.type⟩
        dbg_trace s!"<< deserialized type of {name.proj₂}"
        let params := induct.anon.params
        let indices := induct.anon.indices
        let recr := induct.anon.recr
        let safe := induct.anon.safe
        let refl := induct.anon.refl
        let unit := inductiveIsUnit induct.anon

        let indBlockMeta ← match indBlock.meta with
        | .mutIndBlock x => pure x
        | _ => throw $ .invalidMutIndBlock indBlock.meta.ctorName

        let mut constList : List (Nat × Name) := []
        for ind in indBlockMeta do
          let indIdx ← getDefnIdx ind.name.proj₂
          let indTup := (indIdx, ind.name.proj₂)
          let ctorTups : List (Nat × Name) ← ind.ctors.mapM fun ctor => do
            let name := ctor.name
            let indIdx ← getDefnIdx name
            return (indIdx, name)
          let recTups : List (Nat × Name) ← ind.recrs.mapM fun ⟨_, recr⟩ => do
            let name := recr.name
            let indIdx ← getDefnIdx name
            return (indIdx, name)
          let addList := (indTup :: ctorTups).append recTups
          constList := constList.append addList
        
        let mut recrCtx := default
        for (i, tup) in constList.enum do recrCtx := recrCtx.insert i tup

        -- TODO optimize
        withRecrs recrCtx do
          let struct ← inductiveIsStructure induct
          pure $ .inductive { name, lvls, type, params, indices, recr, safe, refl, unit, struct }
      | .opaque opaqueAnon, .opaque opaqueMeta =>
        let name := opaqueMeta.name
        let lvls := opaqueMeta.lvls
        let type ← exprFromIpld ⟨opaqueAnon.type, opaqueMeta.type⟩
        let value ← exprFromIpld ⟨opaqueAnon.value, opaqueMeta.value⟩
        let safe := opaqueAnon.safe
        pure $ .opaque { name, lvls, type, value, safe }
      | .definition definitionAnon, .definition definitionMeta =>
        dbg_trace s!"\tDefinition case"
        let name := definitionMeta.name
        let lvls := definitionMeta.lvls
        let type ← exprFromIpld ⟨definitionAnon.type, definitionMeta.type⟩
        let value ← exprFromIpld ⟨definitionAnon.value, definitionMeta.value⟩
        let safety := definitionAnon.safety
        pure $ .definition { name, lvls, type, value, safety }
      | .definitionProj definitionAnon, .definitionProj definitionMeta =>
        dbg_trace s!"\tDefinition projection case"
        let defn ← getDefinition (← Key.find $ .const_store ⟨definitionAnon.block, definitionMeta.block⟩) definitionAnon.idx
        let name := defn.meta.name
        let lvls := defn.meta.lvls
        -- TODO correctly substitute free variables with mutual definitions
        let type ← exprFromIpld ⟨defn.anon.type, defn.meta.type⟩
        let value ← exprFromIpld ⟨defn.anon.value, defn.meta.value⟩
        let safety := defn.anon.safety
        pure $ .definition { name, lvls, type, value, safety }
      | .constructorProj anon, .constructorProj meta =>
        let induct ← getInductive (← Key.find $ .const_store ⟨anon.block, meta.block⟩) anon.idx
        let constructorAnon ← ConvertM.unwrap $ induct.anon.ctors.get? anon.cidx;
        let constructorMeta ← ConvertM.unwrap $ induct.meta.ctors.get? anon.cidx;
        let name := constructorMeta.name
        let lvls := constructorMeta.lvls
        let type ← exprFromIpld ⟨constructorAnon.type, constructorMeta.type⟩
        let idx    := constructorAnon.idx
        let params := constructorAnon.params
        let fields := constructorAnon.fields
        -- TODO correctly substitute free variables of `rhs` with inductives, constructors and recursors
        let rhs ← exprFromIpld ⟨constructorAnon.rhs, constructorMeta.rhs⟩
        let safe := constructorAnon.safe
        pure $ .constructor { name, lvls, type, idx, params, fields, rhs, safe }
      | .recursorProj anon, .recursorProj meta =>
        let induct ← getInductive (← Key.find $ .const_store ⟨anon.block, meta.block⟩) anon.idx
        let pairAnon ← ConvertM.unwrap $ induct.anon.recrs.get? anon.ridx;
        let pairMeta ← ConvertM.unwrap $ induct.meta.recrs.get? anon.ridx;
        let recursorAnon := Sigma.snd pairAnon
        let recursorMeta := Sigma.snd pairMeta
        let name := recursorMeta.name
        let lvls := recursorMeta.lvls
        -- TODO correctly substitute free variables of `type` with inductives, constructors and recursors
        let type ← exprFromIpld ⟨recursorAnon.type, recursorMeta.type⟩
        let params := recursorAnon.params
        let indices := recursorAnon.indices
        let motives := recursorAnon.motives
        let minors := recursorAnon.minors
        let k := recursorAnon.k
        let casesExtInt : (b₁ : RecType) → (b₂ : RecType) → (Ipld.Recursor b₁ .Anon) → (Ipld.Recursor b₂ .Meta) → ConvertM Const
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
      Key.store (.const_cache cid) constIdx
      let defns := (← get).defns
      let maxSize := defns.size
      if h : constIdx < maxSize then
        set { ← get with defns := defns.set ⟨constIdx, h⟩ const }
      else
        throw $ .constIdxOutOfRange constIdx maxSize
      dbg_trace s!"-------------- FINISHED PROCESSING {meta.name}"
      pure constIdx

  partial def ctorFromIpld (ctor : Ipld.Both Ipld.Constructor) : ConvertM Constructor := do
    let name := ctor.meta.name
    let lvls := ctor.meta.lvls
    dbg_trace s!">> deserializing type of {ctor.meta.name.proj₂}"
    let type ← exprFromIpld ⟨ctor.anon.type, ctor.meta.type⟩
    dbg_trace s!"<< deserialized type of {ctor.meta.name.proj₂}"
    dbg_trace s!">> deserializing rhs of {ctor.meta.name.proj₂}"
    let rhs ← exprFromIpld ⟨ctor.anon.rhs, ctor.meta.rhs⟩
    dbg_trace s!"<< deserialized rhs of {ctor.meta.name.proj₂}"
    let idx := ctor.anon.idx
    let params := ctor.anon.fields
    let fields := ctor.anon.params
    let safe := ctor.anon.safe
    pure { name, lvls, type, idx, params, fields, rhs, safe }

  partial def ruleFromIpld (rule : Ipld.Both Ipld.RecursorRule) : ConvertM RecursorRule := do
    let rhs ← exprFromIpld ⟨rule.anon.rhs, rule.meta.rhs⟩
    let ctorIdx ← constFromIpld ⟨rule.anon.ctor, rule.meta.ctor⟩
    let defns := (← get).defns
    let maxSize := defns.size
    if h : ctorIdx < maxSize then
      let ctor ← match defns[ctorIdx]'h with
        | .constructor ctor => pure ctor
        | _ => throw .ipldError
      return { rhs, ctor, fields := rule.anon.fields }
    else
      throw $ .constIdxOutOfRange ctorIdx maxSize

end

def convertStore (store : Ipld.Store) : Except ConvertError ConvertState :=
  ConvertM.run (ConvertEnv.init store) default do
    (← read).store.const_meta.toList.enum.forM fun (idx, (_, meta)) => do
      modifyGet fun state => (default, { state with
        defns := state.defns.push default,
        defnsIdx := state.defnsIdx.insert meta.name idx })
    (← read).store.defns.forM fun cid => discard $ constFromIpld cid

def extractConstArray (store : Ipld.Store) : Except String (Array Const) :=
  match convertStore store with
  | .ok stt => pure stt.defns
  | .error err => .error $ toString err

end FromIpld
end Yatima
