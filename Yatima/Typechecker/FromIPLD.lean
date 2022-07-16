import Yatima.Store
import Yatima.Typechecker.Expr
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
deriving Inhabited

instance : ToString ConvertError where
  toString
    | .cannotFindAnon => "Cannot find anon"
    | .cannotFindMeta => "Cannot find meta"
    | .anonMetaMismatch => "Anon/meta are of different kind"
    | .ipldError => "IPLD broken"
    | .cannotStoreValue => "Cannot store value"

structure ConvertState where
  expr_cache : RBMap ExprCid Expr compare
  const_cache : RBMap ConstCid Const compare
  univ_cache : RBMap UnivCid Univ compare
instance : Inhabited ConvertState where
  default := .mk .empty .empty .empty

abbrev ConvertM := ReaderT Store <| EStateM ConvertError ConvertState
instance : Monad ConvertM := let i := inferInstanceAs (Monad ConvertM); { pure := i.pure, bind := i.bind }
instance (α : Type) : Inhabited (ConvertM α) where
  default _ := throw .ipldError

def ConvertM.run (env : Store) (ste : ConvertState) (m : ConvertM α) : Except ConvertError α :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok a _  => .ok a
  | .error e _ => .error e

def ConvertM.unwrap : Option A → ConvertM A := Option.option (throw .ipldError) pure

-- Auxiliary definitions
inductive Key : Type → Type
  | univ_cache  : UnivCid      → Key Univ
  | expr_cache  : ExprCid      → Key Expr
  | const_cache : ConstCid     → Key Const
  | univ_anon   : UnivAnonCid  → Key UnivAnon
  | expr_anon   : ExprAnonCid  → Key ExprAnon
  | const_anon  : ConstAnonCid → Key ConstAnon
  | univ_meta   : UnivMetaCid  → Key UnivMeta
  | expr_meta   : ExprMetaCid  → Key ExprMeta
  | const_meta  : ConstMetaCid → Key ConstMeta

def Key.find? : (key : Key A) → ConvertM (Option A)
  | .univ_cache  univ  => do pure $ (← get).univ_cache.find? univ
  | .expr_cache  expr  => do pure $ (← get).expr_cache.find? expr
  | .const_cache const => do pure $ (← get).const_cache.find? const
  | .univ_anon   univ  => do pure $ (← read).univ_anon.find? univ
  | .expr_anon   expr  => do pure $ (← read).expr_anon.find? expr
  | .const_anon  const => do pure $ (← read).const_anon.find? const
  | .univ_meta   univ  => do pure $ (← read).univ_meta.find? univ
  | .expr_meta   expr  => do pure $ (← read).expr_meta.find? expr
  | .const_meta  const => do pure $ (← read).const_meta.find? const

def Key.find (key : Key A) : ConvertM A := do
  ConvertM.unwrap (← Key.find? key)

def Key.store : (Key A) → A → ConvertM Unit
  | .univ_cache  univ, a  => modifyGet (fun stt => (() , { stt with univ_cache  := stt.univ_cache.insert univ a }))
  | .expr_cache  expr, a  => modifyGet (fun stt => (() , { stt with expr_cache  := stt.expr_cache.insert expr a }))
  | .const_cache const, a => modifyGet (fun stt => (() , { stt with const_cache := stt.const_cache.insert const a }))
  | _, _ => throw .cannotStoreValue

def getInductive : (b : Bool) → (if b then Yatima.ConstAnon else Yatima.ConstMeta) → Nat → ConvertM (if b then Yatima.InductiveAnon else Yatima.InductiveMeta)
  | .true, .mutIndBlock inds, idx => pure $ inds.get! idx
  | .false, .mutIndBlock inds, idx => pure $ inds.get! idx
  | _, _, _ => throw .ipldError

def getInductiveAnon := getInductive True
def getInductiveMeta := getInductive False

def List.zipWithError [Monad m] [MonadExcept ε m] (e : ε) (f : α → β → m γ) : List α → List β → m (List γ)
  | x::xs, y::ys => do
    let z ← f x y
    let zs ← List.zipWithError e f xs ys
    pure $ z :: zs
  | [], []     => pure []
  | _, _     => throw e

-- Conversion functions
partial def univFromIpld (anonCid : UnivAnonCid) (metaCid : UnivMetaCid) : ConvertM Univ := do
  let cid := .mk anonCid metaCid
  match <- Key.find? $ .univ_cache $ cid with
  | none => pure ()
  | some univ => return univ
  let anon ← Key.find $ .univ_anon  anonCid
  let meta ← Key.find $ .univ_meta metaCid
  let univ ← match (anon, meta) with
  | (.zero, .zero) => pure $ .zero
  | (.succ univAnon, .succ univMeta) => pure $ .succ (← univFromIpld univAnon univMeta)
  | (.max univAnon₁ univAnon₂, .max univMeta₁ univMeta₂) =>
    pure $ .max (← univFromIpld univAnon₁ univMeta₁) (← univFromIpld univAnon₂ univMeta₂)
  | (.imax univAnon₁ univAnon₂, .imax univMeta₁ univMeta₂) =>
    pure $ .imax (← univFromIpld univAnon₁ univMeta₁) (← univFromIpld univAnon₂ univMeta₂)
  | (.param idx, .param nam) => pure $ .var nam idx
  | _ => throw .anonMetaMismatch
  Key.store (.univ_cache cid) univ
  pure univ

partial def univsFromIpld (anonCids : List UnivAnonCid) (metaCids : List UnivMetaCid) : ConvertM (List Univ) := do
  List.zipWithError .anonMetaMismatch univFromIpld anonCids metaCids

def inductiveIsUnit (ind : InductiveAnon) : Bool :=
  if ind.recr || ind.indices != 0 then false
  else match ind.ctors with
  | [ctor] => ctor.fields != 0
  | _ => false

mutual
partial def exprFromIpld (anonCid : ExprAnonCid) (metaCid : ExprMetaCid) : ConvertM Expr := do
  let cid := .mk anonCid metaCid
  match <- Key.find? $ .expr_cache $ cid with
  | none => pure ()
  | some expr => return expr
  let anon ← Key.find $ .expr_anon anonCid
  let meta ← Key.find $ .expr_meta metaCid
  let expr ← match (anon, meta) with
  | (.var idx, .var name) => pure $ .var anonCid name idx
  | (.sort uAnonCid, .sort uMetaCid) => pure $ .sort anonCid (← univFromIpld uAnonCid uMetaCid)
  | (.const cAnonCid uAnonCids, .const name cMetaCid uMetaCids) =>
    let const ← constFromIpld cAnonCid cMetaCid
    let univs ← List.zipWithError .anonMetaMismatch univFromIpld uAnonCids uMetaCids
    pure $ .const anonCid name const univs
  | (.app fncAnon argAnon, .app fncMeta argMeta) =>
    let fnc ← exprFromIpld fncAnon fncMeta
    let arg ← exprFromIpld argAnon argMeta
    pure $ .app anonCid fnc arg
  | (.lam domAnon bodAnon, .lam name binfo domMeta bodMeta) =>
    let dom ← exprFromIpld domAnon domMeta
    let bod ← exprFromIpld bodAnon bodMeta
    pure $ .lam anonCid name binfo dom bod
  | (.pi domAnon codAnon, .pi name binfo domMeta codMeta) =>
    let dom ← exprFromIpld domAnon domMeta
    let cod ← exprFromIpld codAnon codMeta
    pure $ .pi anonCid name binfo dom cod
  | (.letE typAnon valAnon bodAnon, .letE name typMeta valMeta bodMeta) =>
    let typ ← exprFromIpld typAnon typMeta
    let val ← exprFromIpld valAnon valMeta
    let bod ← exprFromIpld bodAnon bodMeta
    pure $ .letE anonCid name typ val bod
  | (.lit lit, .lit) => pure $ .lit anonCid lit
  | (.lty lty, .lty) => pure $ .lty anonCid lty
  | (.fix bodAnon, .fix name bodMeta) =>
    let bod ← exprFromIpld bodAnon bodMeta
    pure $ .fix anonCid name bod
  | (.proj idx bodAnon, .proj _ bodMeta) =>
    let bod ← exprFromIpld bodAnon bodMeta
    pure $ .proj anonCid idx bod
  | _ => throw .anonMetaMismatch
  Key.store (.expr_cache cid) expr
  pure expr

partial def constFromIpld (anonCid : ConstAnonCid) (metaCid : ConstMetaCid) : ConvertM Const := do
  let cid := .mk anonCid metaCid
  match <- Key.find? $ .const_cache $ cid with
  | none => pure ()
  | some const => return const
  let anon ← Key.find $ .const_anon anonCid
  let meta ← Key.find $ .const_meta metaCid
  let const ← match (anon, meta) with
  | (.axiom axiomAnon, .axiom axiomMeta) =>
    let name := axiomMeta.name
    let lvls := axiomMeta.lvls
    let type ← exprFromIpld axiomAnon.type axiomMeta.type
    let safe := axiomAnon.safe
    pure $ .axiom anonCid { name, lvls, type, safe }
  | (.theorem theoremAnon, .theorem theoremMeta) =>
    let name := theoremMeta.name
    let lvls := theoremMeta.lvls
    let type ← exprFromIpld theoremAnon.type theoremMeta.type
    let value ← exprFromIpld theoremAnon.value theoremMeta.value
    pure $ .theorem anonCid { name, lvls, type, value }
  | (.inductiveProj anon, .inductiveProj meta) =>
    let inductiveAnon ← getInductiveAnon (← Key.find $ .const_anon anon.block) anon.idx
    let inductiveMeta ← getInductiveMeta (← Key.find $ .const_meta meta.block) anon.idx
    let name := inductiveMeta.name
    let lvls := inductiveMeta.lvls
    let type ← exprFromIpld inductiveAnon.type inductiveMeta.type
    let params := inductiveAnon.params
    let indices := inductiveAnon.indices
    let ctors ← List.zipWithError .anonMetaMismatch ctorFromIpld inductiveAnon.ctors inductiveMeta.ctors
    let recr := inductiveAnon.recr
    let safe := inductiveAnon.safe
    let refl := inductiveAnon.refl
    let unit := inductiveIsUnit inductiveAnon
    pure $ .inductive anonCid { name, lvls, type, params, indices, ctors, recr, safe, refl, unit }
  | (.opaque opaqueAnon, .opaque opaqueMeta) =>
    let name := opaqueMeta.name
    let lvls := opaqueMeta.lvls
    let type ← exprFromIpld opaqueAnon.type opaqueMeta.type
    let value ← exprFromIpld opaqueAnon.value opaqueMeta.value
    let safe := opaqueAnon.safe
    pure $ .opaque anonCid { name, lvls, type, value, safe }
  | (.definition definitionAnon, .definition definitionMeta) =>
    let name := definitionMeta.name
    let lvls := definitionMeta.lvls
    let type ← exprFromIpld definitionAnon.type definitionMeta.type
    let value ← exprFromIpld definitionAnon.value definitionMeta.value
    let safety := definitionAnon.safety
    pure $ .definition anonCid { name, lvls, type, value, safety }
  | (.constructorProj anon, .constructorProj meta) =>
    let inductiveAnon ← getInductiveAnon (← Key.find $ .const_anon anon.block) anon.idx
    let inductiveMeta ← getInductiveMeta (← Key.find $ .const_meta meta.block) anon.idx
    let constructorAnon ← ConvertM.unwrap $ inductiveAnon.ctors.get? anon.cidx;
    let constructorMeta ← ConvertM.unwrap $ inductiveMeta.ctors.get? anon.cidx;
    let name := constructorMeta.name
    let type ← exprFromIpld constructorAnon.type constructorMeta.type
    let params := constructorAnon.params
    let fields := constructorAnon.fields
    -- TODO correctly substitute free variables of `rhs` with inductives, constructors and recursors
    let rhs ← exprFromIpld constructorAnon.rhs constructorMeta.rhs
    pure $ .constructor anonCid { name, type, params, fields, rhs }
  | (.recursorProj anon, .recursorProj meta) =>
    let inductiveAnon ← getInductiveAnon (← Key.find $ .const_anon anon.block) anon.idx
    let inductiveMeta ← getInductiveMeta (← Key.find $ .const_meta meta.block) anon.idx
    let pairAnon ← ConvertM.unwrap $ inductiveAnon.recrs.get? anon.ridx;
    let pairMeta ← ConvertM.unwrap $ inductiveMeta.recrs.get? anon.ridx;
    let recursorAnon := Sigma.snd pairAnon
    let recursorMeta := Sigma.snd pairMeta
    let name := recursorMeta.name
    let lvls := recursorMeta.lvls
    let type ← exprFromIpld recursorAnon.type recursorMeta.type
    let params := recursorAnon.params
    let indices := recursorAnon.indices
    let motives := recursorAnon.motives
    let minors := recursorAnon.minors
    let k := recursorAnon.k
    let casesExtInt : (b₁ : Bool) → (b₂ : Bool) → (RecursorAnon b₁) → (RecursorMeta b₂) → ConvertM Const 
    | .true, .true, _, _ => pure $ .intRecursor anonCid { name, lvls, type, params, indices, motives, minors, k }
    | .false, .false, recAnon, recMeta => do
      let rules ← List.zipWithError .anonMetaMismatch ruleFromIpld recAnon.rules recMeta.rules
      pure $ .extRecursor anonCid { name, lvls, type, params, indices, motives, minors, rules, k }
    | _, _, _, _ => throw .ipldError
    casesExtInt (Sigma.fst pairAnon) (Sigma.fst pairMeta) recursorAnon recursorMeta
  | (.quotient quotientAnon, .quotient quotientMeta) =>
    let name := quotientMeta.name
    let lvls := quotientMeta.lvls
    let type ← exprFromIpld quotientAnon.type quotientMeta.type
    let kind := quotientAnon.kind
    pure $ .quotient anonCid { name, lvls, type, kind }
  | _ => throw .anonMetaMismatch
  Key.store (.const_cache cid) const
  pure const

partial def ctorFromIpld (ctorAnon : ConstructorAnon) (ctorMeta : ConstructorMeta) : ConvertM (Constructor Expr) := do
  let type ← exprFromIpld ctorAnon.type ctorMeta.type
  let rhs ← exprFromIpld ctorAnon.rhs ctorMeta.rhs
  pure { name := ctorMeta.name, type, params := ctorAnon.params, fields := ctorAnon.fields, rhs }

partial def ruleFromIpld (ruleAnon : RecursorRuleAnon) (ruleMeta : RecursorRuleMeta) : ConvertM (RecursorRule Expr) := do
  let rhs ← exprFromIpld ruleAnon.rhs ruleMeta.rhs
  pure $ { rhs, ctor := ruleAnon.ctor, fields := ruleAnon.fields }
end

def convertStore (store : Store) : Except ConvertError (List Expr) := ConvertM.run store default $ do
  let cidMap := (← read).expr_cache
  let collect := fun exprs cid _ => do
    let expr ← exprFromIpld cid.anon cid.meta
    pure $ expr :: exprs
  cidMap.foldM collect []

def convertStoreIO (store : Store) : IO (List Expr) :=
  match convertStore store with
  | .ok exprs => pure exprs
  | .error err => .error $ toString err

end Yatima.Typechecker
