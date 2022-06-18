import Yatima.Env
import Yatima.Typechecker.Expr

namespace Yatima.Typechecker

open Std (RBMap)
-- structure CompileState where
--   env   : Yatima.Env
--   cache : RBMap Name Const Ord.compare

-- instance : Inhabited CompileState where
--   default := ⟨default, .empty⟩

-- structure CompileEnv where
--   constMap    : Lean.ConstMap
--   bindCtx     : List Name
--   printLean   : Bool
--   printYatima : Bool
--   deriving Inhabited
-- abbrev ConvM := ReaderT Context <| StateT ConstMap Id
inductive ConvError where
| cannotFindAnon : ConvError
| cannotFindMeta : ConvError
| anonMetaMismatch : ConvError
| todo : ConvError
deriving Inhabited

abbrev ConvM := ReaderT Env <| ExceptT ConvError Id

def findAnon (anonCid : ExprAnonCid) : ConvM ExprAnon := do
  match (← read).expr_anon.find? anonCid with
  | .some expr => pure expr
  | .none => throw .cannotFindAnon

def findMeta (metaCid : ExprMetaCid) : ConvM ExprMeta := do
  match (← read).expr_meta.find? metaCid with
  | .some expr => pure expr
  | .none => throw .cannotFindMeta

def constFromIpld (anonCid : ConstAnonCid) (metaCid : ConstMetaCid) : ConvM Const := do
  throw .todo

def univFromIpld (anonCid : UnivAnonCid) (metaCid : UnivMetaCid) : ConvM Univ := do
  throw .todo

def univsFromIpld (anonCids : List UnivAnonCid) (metaCids : List UnivMetaCid) : ConvM (List Univ) := do
  throw .todo

partial def exprFromIpld (anonCid : ExprAnonCid) (metaCid : ExprMetaCid) : ConvM Expr := do
  let anon ← findAnon anonCid
  let meta ← findMeta metaCid
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
