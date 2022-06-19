import Yatima.Env
import Yatima.Typechecker.Expr

namespace Yatima.Typechecker

-- Conversion monad
inductive ConvError where
| cannotFindAnon : ConvError
| cannotFindMeta : ConvError
| anonMetaMismatch : ConvError
deriving Inhabited

abbrev ConvM := ReaderT Env <| ExceptT ConvError Id

-- Auxiliary functions
def findExprAnon (anonCid : ExprAnonCid) : ConvM ExprAnon := do
  match (← read).expr_anon.find? anonCid with
  | .some expr => pure expr
  | .none => throw .cannotFindAnon

def findExprMeta (metaCid : ExprMetaCid) : ConvM ExprMeta := do
  match (← read).expr_meta.find? metaCid with
  | .some expr => pure expr
  | .none => throw .cannotFindMeta

def findConstAnon (anonCid : ConstAnonCid) : ConvM ConstAnon := do
  match (← read).const_anon.find? anonCid with
  | .some const => pure const
  | .none => throw .cannotFindAnon

def findConstMeta (metaCid : ConstMetaCid) : ConvM ConstMeta := do
  match (← read).const_meta.find? metaCid with
  | .some const => pure const
  | .none => throw .cannotFindMeta

def findUnivAnon (anonCid : UnivAnonCid) : ConvM UnivAnon := do
  match (← read).univ_anon.find? anonCid with
  | .some univ => pure univ
  | .none => throw .cannotFindAnon

def findUnivMeta (metaCid : UnivMetaCid) : ConvM UnivMeta := do
  match (← read).univ_meta.find? metaCid with
  | .some univ => pure univ
  | .none => throw .cannotFindMeta

-- Conversion functions
partial def univFromIpld (anonCid : UnivAnonCid) (metaCid : UnivMetaCid) : ConvM Univ := do
  let anon ← findUnivAnon anonCid
  let meta ← findUnivMeta metaCid
  match (anon, meta) with
  | (.zero, .zero) => pure $ .zero
  | (.succ univAnon, .succ univMeta) => pure $ .succ (← univFromIpld univAnon univMeta)
  | (.max univAnon₁ univAnon₂, .max univMeta₁ univMeta₂) =>
    pure $ .max (← univFromIpld univAnon₁ univMeta₂) (← univFromIpld univAnon₁ univMeta₂)
  | (.imax univAnon₁ univAnon₂, .imax univMeta₁ univMeta₂) =>
    pure $ .imax (← univFromIpld univAnon₁ univMeta₂) (← univFromIpld univAnon₁ univMeta₂)
  | (.param idx, .param nam) => pure $ .var nam idx
  | _ => throw .anonMetaMismatch

partial def univsFromIpld (anonCids : List UnivAnonCid) (metaCids : List UnivMetaCid) : ConvM (List Univ) := do
  match (anonCids, metaCids) with
  | (anonCid :: anonCids, metaCid :: metaCids) =>
    pure $ (← univFromIpld anonCid metaCid) :: (← univsFromIpld anonCids metaCids)
  | ([], []) => pure []
  | _ => throw .anonMetaMismatch

def inductiveIsUnit (ctors : List (Name × ExprAnonCid)) : ConvM Bool := pure false -- TODO

mutual
partial def exprFromIpld (anonCid : ExprAnonCid) (metaCid : ExprMetaCid) : ConvM Expr := do
  let anon ← findExprAnon anonCid
  let meta ← findExprMeta metaCid
  match (anon, meta) with
  | (.var idx, .var name) => pure $ .var anonCid name idx
  | (.sort uAnonCid, .sort uMetaCid) => pure $ .sort anonCid (← univFromIpld uAnonCid uMetaCid)
  | (.const cAnonCid uAnonCids, .const name cMetaCid uMetaCids) =>
    let const ← constFromIpld cAnonCid cMetaCid
    let univs ← univsFromIpld uAnonCids uMetaCids
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

partial def constFromIpld (anonCid : ConstAnonCid) (metaCid : ConstMetaCid) : ConvM Const := do
  let anon ← findConstAnon anonCid
  let meta ← findConstMeta metaCid
  match (anon, meta) with
  | (.«axiom» axiomAnon, .«axiom» axiomMeta) =>
    let name := axiomMeta.name
    let lvls := axiomMeta.lvls
    let type ← exprFromIpld axiomAnon.type axiomMeta.type
    let safe := axiomAnon.safe
    pure $ .«axiom» anonCid { name, lvls, type, safe }
  | (.«theorem» theoremAnon, .«theorem» theoremMeta) =>
    let name := theoremMeta.name
    let lvls := theoremMeta.lvls
    let type ← exprFromIpld theoremAnon.type theoremMeta.type
    let value ← exprFromIpld theoremAnon.value theoremMeta.value
    pure $ .«theorem» anonCid { name, lvls, type, value }
  | (.«inductive» inductiveAnon, .«inductive» inductiveMeta) =>
    let name := inductiveMeta.name
    let lvls := inductiveMeta.lvls
    let type ← exprFromIpld inductiveAnon.type inductiveMeta.type
    let params := inductiveAnon.params
    let indices := inductiveAnon.indices
    let ctors ← ctorsFromIpld inductiveAnon.ctors inductiveMeta.ctors
    let recr := inductiveAnon.recr
    let safe := inductiveAnon.safe
    let refl := inductiveAnon.refl
    let nest := inductiveAnon.nest
    let unit ← inductiveIsUnit inductiveAnon.ctors
    pure $ .«inductive» anonCid { name, lvls, type, params, indices, ctors, recr, safe, refl, nest, unit }
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
  | (.constructor constructorAnon, .constructor constructorMeta) =>
    let name := constructorMeta.name
    let lvls := constructorMeta.lvls
    let type ← exprFromIpld constructorAnon.type constructorMeta.type
    let params := constructorAnon.params
    let idx := constructorAnon.idx
    let fields := constructorAnon.fields
    let safe := constructorAnon.safe
    pure $ .constructor anonCid { name, lvls, type, idx, params, fields, safe }
  | (.recursor recursorAnon, .recursor recursorMeta) =>
    let name := recursorMeta.name
    let lvls := recursorMeta.lvls
    let type ← exprFromIpld recursorAnon.type recursorMeta.type
    let params := recursorAnon.params
    let indices := recursorAnon.indices
    let motives := recursorAnon.motives
    let minors := recursorAnon.minors
    let rules ← rulesFromIpld recursorAnon.rules recursorMeta.rules
    let k := recursorAnon.k
    let safe := recursorAnon.safe
    pure $ .recursor anonCid { name, lvls, type, params, indices, motives, minors, rules, k, safe }
  | (.quotient quotientAnon, .quotient quotientMeta) =>
    let name := quotientMeta.name
    let lvls := quotientMeta.lvls
    let type ← exprFromIpld quotientAnon.type quotientMeta.type
    let kind := quotientAnon.kind
    pure $ .quotient anonCid { name, lvls, type, kind }
  | _ => throw .anonMetaMismatch

partial def ctorsFromIpld (ctorsAnon : List (Name × ExprAnonCid)) (ctorsMeta : List ExprMetaCid) : ConvM (List (Name × Expr)) :=
  match (ctorsAnon, ctorsMeta) with
  | ((name, exprAnon) :: ctorsAnon, exprMeta :: ctorsMeta) => do
    let expr ← exprFromIpld exprAnon exprMeta
    let ctors ← ctorsFromIpld ctorsAnon ctorsMeta
    pure $ (name, expr) :: ctors
  | ([], []) => pure []
  | _ => throw .anonMetaMismatch

partial def rulesFromIpld (rulesAnon : List RecursorRuleAnon) (rulesMeta : List RecursorRuleMeta) : ConvM (List (RecursorRule Expr)) :=
  match (rulesAnon, rulesMeta) with
  | (ruleAnon :: rulesAnon, ruleMeta :: rulesMeta) => do
    let rhs ← exprFromIpld ruleAnon.rhs ruleMeta.rhs
    let rules ← rulesFromIpld rulesAnon rulesMeta
    pure $ { rhs, ctor := ruleAnon.ctor, fields := ruleAnon.fields } :: rules
  | ([], []) => pure []
  | _ => throw .anonMetaMismatch
end

end Yatima.Typechecker
