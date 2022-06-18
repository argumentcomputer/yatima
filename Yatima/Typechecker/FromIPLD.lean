import Yatima.Env
import Yatima.Typechecker.Expr

namespace Yatima.Typechecker

-- Conversion monad
inductive ConvError where
| cannotFindAnon : ConvError
| cannotFindMeta : ConvError
| anonMetaMismatch : ConvError
| todo : ConvError
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

partial def constFromIpld (anonCid : ConstAnonCid) (metaCid : ConstMetaCid) : ConvM Const := do
  throw .todo

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

end Yatima.Typechecker
