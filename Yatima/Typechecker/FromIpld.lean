import Yatima.Datatypes.Store
import YatimaStdLib.RBMap

namespace Yatima.Typechecker

open Std (RBMap)

-- Conversion monad
inductive ConvertError where
  | cannotFindAnon : ConvertError
  | cannotFindMeta : ConvertError
  | anonMetaMismatch : ConvertError
  | ipldError : ConvertError
  | cannotStoreValue : ConvertError
  | mutDefBlockFound : ConvertError
  | mutIndBlockFound : ConvertError
  deriving Inhabited

instance : ToString ConvertError where toString
  | .cannotFindAnon => "Cannot find anon"
  | .cannotFindMeta => "Cannot find meta"
  | .anonMetaMismatch => "Anon/meta are of different kind"
  | .ipldError => "IPLD broken"
  | .cannotStoreValue => "Cannot store value"
  | .mutDefBlockFound => "Found a mutual definition block inside an expression"
  | .mutIndBlockFound => "Found a mutual inductive block inside an expression"

structure ConvertState where
  univ_cache  : RBMap UnivCid Univ compare
  expr_cache  : RBMap ExprCid Expr compare
  const_cache : RBMap ConstCid ConstIdx compare
  defns       : Array Const
  deriving Inhabited

abbrev ConvertM := ReaderT Ipld.Store <| EStateM ConvertError ConvertState

instance : Monad ConvertM :=
  let i := inferInstanceAs (Monad ConvertM)
  { pure := i.pure, bind := i.bind }

instance (α : Type) : Inhabited (ConvertM α) where
  default _ := throw .ipldError

def ConvertM.run (env : Ipld.Store) (ste : ConvertState) (m : ConvertM α) :
    Except ConvertError ConvertState :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ stt  => .ok stt
  | .error e _ => .error e

def ConvertM.unwrap : Option A → ConvertM A :=
  Option.option (throw .ipldError) pure

-- Auxiliary definitions
inductive Key : Type → Type
  | univ_cache  : UnivCid  → Key Univ
  | expr_cache  : ExprCid  → Key Expr
  | const_cache : ConstCid → Key ConstIdx
  | univ_store  : UnivCid  → Key (Ipld.Both Ipld.Univ)
  | expr_store  : ExprCid  → Key (Ipld.Both Ipld.Expr)
  | const_store : ConstCid → Key (Ipld.Both Ipld.Const)

def Key.find? : (key : Key A) → ConvertM (Option A)
  | .univ_cache  univ  => do pure $ (← get).univ_cache.find? univ
  | .expr_cache  expr  => do pure $ (← get).expr_cache.find? expr
  | .const_cache const => do pure $ (← get).const_cache.find? const
  | .univ_store  univ  => do
    let ctx ← read
    let anon? := ctx.univ_anon.find? univ.anon
    let meta? := ctx.univ_meta.find? univ.meta
    match anon?, meta? with
    | some anon, some meta => pure $ some ⟨anon, meta⟩
    | _, _ => pure none
  | .expr_store  expr  => do
    let ctx ← read
    let anon? := ctx.expr_anon.find? expr.anon
    let meta? := ctx.expr_meta.find? expr.meta
    match anon?, meta? with
    | some anon, some meta => pure $ some ⟨anon, meta⟩
    | _, _ => pure none
  | .const_store const => do
    let ctx ← read
    let anon? := ctx.const_anon.find? const.anon
    let meta? := ctx.const_meta.find? const.meta
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
      | _, _ => throw .anonMetaMismatch
    Key.store (.univ_cache cid) univ
    pure univ
  | some univ => pure univ

def inductiveIsUnit (ind : Ipld.Inductive .Anon) : Bool :=
  if ind.recr || ind.indices.proj₁ != 0 then false
  else match ind.ctors with
    | [ctor] => ctor.fields.proj₁ == 0
    | _ => false

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
        | .var () idx, .var name () => pure $ .var name.proj₂ idx
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
          let dom ← exprFromIpld ⟨domAnon, domMeta⟩
          let bod ← exprFromIpld ⟨bodAnon, bodMeta⟩
          pure $ .lam name binfo dom bod
        | .pi () binfo domAnon codAnon, .pi name () domMeta codMeta =>
          let dom ← exprFromIpld ⟨domAnon, domMeta⟩
          let cod ← exprFromIpld ⟨codAnon, codMeta⟩
          pure $ .pi name binfo dom cod
        | .letE () typAnon valAnon bodAnon, .letE name typMeta valMeta bodMeta =>
          let typ ← exprFromIpld ⟨typAnon, typMeta⟩
          let val ← exprFromIpld ⟨valAnon, valMeta⟩
          let bod ← exprFromIpld ⟨bodAnon, bodMeta⟩
          pure $ .letE name typ val bod
        | .lit lit, .lit () => pure $ .lit lit
        | .lty lty, .lty () => pure $ .lty lty
        | .proj idx bodAnon, .proj () bodMeta =>
          let bod ← exprFromIpld ⟨bodAnon, bodMeta⟩
          pure $ .proj idx bod
        | _, _ => throw .anonMetaMismatch
      Key.store (.expr_cache cid) expr
      pure expr

  partial def constFromIpld (cid : Ipld.Both Ipld.ConstCid) :
      ConvertM ConstIdx := do
    match ← Key.find? (.const_cache cid) with
    | some constIdx => pure constIdx
    | none =>
      let constIdx ← modifyGet (fun stt => (stt.defns.size, { stt with defns := stt.defns.push default }))
      let ⟨anon, meta⟩ := ← Key.find $ .const_store cid
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
        let induct ← getInductive (← Key.find $ .const_store ⟨anon.block, meta.block⟩) anon.idx
        let name := induct.meta.name
        let lvls := induct.meta.lvls
        let type ← exprFromIpld ⟨induct.anon.type, induct.meta.type⟩
        let params := induct.anon.params
        let indices := induct.anon.indices
        let recr := induct.anon.recr
        let safe := induct.anon.safe
        let refl := induct.anon.refl
        let unit := inductiveIsUnit induct.anon
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
        let name := definitionMeta.name
        let lvls := definitionMeta.lvls
        let type ← exprFromIpld ⟨definitionAnon.type, definitionMeta.type⟩
        let value ← exprFromIpld ⟨definitionAnon.value, definitionMeta.value⟩
        let safety := definitionAnon.safety
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
        let type ← exprFromIpld ⟨recursorAnon.type, recursorMeta.type⟩
        let params := recursorAnon.params
        let indices := recursorAnon.indices
        let motives := recursorAnon.motives
        let minors := recursorAnon.minors
        let k := recursorAnon.k
        let casesExtInt : (b₁ : RecType) → (b₂ : RecType) → (Ipld.Recursor .Anon b₁) → (Ipld.Recursor .Meta b₂) → ConvertM Const
        | .Intr, .Intr, _, _ => pure $ .intRecursor { name, lvls, type, params, indices, motives, minors, k }
        | .Extr, .Extr, recAnon, recMeta => do
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
      | _, _ => throw .anonMetaMismatch
      Key.store (.const_cache cid) constIdx
      modify (fun stt => { stt with defns := stt.defns.set! constIdx const })
      pure constIdx

  partial def ctorFromIpld (ctor : Ipld.Both Ipld.Constructor) : ConvertM Constructor := do
    let name := ctor.meta.name
    let lvls := ctor.meta.lvls
    let type ← exprFromIpld ⟨ctor.anon.type, ctor.meta.type⟩
    let rhs ← exprFromIpld ⟨ctor.anon.rhs, ctor.meta.rhs⟩
    let idx := ctor.anon.idx
    let params := ctor.anon.fields
    let fields := ctor.anon.params
    let safe := ctor.anon.safe
    pure { name, lvls, type, idx, params, fields, rhs, safe }

  partial def ruleFromIpld (rule : Ipld.Both Ipld.RecursorRule) : ConvertM RecursorRule := do
    let rhs ← exprFromIpld ⟨rule.anon.rhs, rule.meta.rhs⟩
    let ctorIdx ← constFromIpld ⟨rule.anon.ctor, rule.meta.ctor⟩
    let ctor ← match (← get).defns.get! ctorIdx with
      | .constructor ctor => pure ctor
      | _ => throw .ipldError
    pure $ { rhs, ctor, fields := rule.anon.fields }

end

def convertStore (store : Ipld.Store) : Except ConvertError ConvertState :=
  ConvertM.run store default do
    let cidMap := (← read).const_cids
    let catchMut err := match err with
      | .mutDefBlockFound => pure ()
      | .mutIndBlockFound => pure ()
      | _ => throw err
    let collect := fun cid => do
      tryCatch (discard $ constFromIpld cid) catchMut
    cidMap.forM collect

def extractConstArray (store : Ipld.Store) : Except String (Array Const) :=
  match convertStore store with
  | .ok stt => pure stt.defns
  | .error err => .error $ toString err

end Yatima.Typechecker
