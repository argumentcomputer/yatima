import Yatima.Transpiler.TranspileM

namespace Yatima.Transpiler

inductive StoreKey : Type → Type
  | univ  : Ipld.Both Ipld.UnivCid  → StoreKey (Ipld.Both Ipld.Univ)
  | expr  : Ipld.Both Ipld.ExprCid  → StoreKey (Ipld.Both Ipld.Expr)
  | const : Ipld.Both Ipld.ConstCid → StoreKey (Ipld.Both Ipld.Const)

def StoreKey.find? : (key : StoreKey A) → TranspileM (Option A)
  | .univ  univCid => do
    let store := (← read).store
    match store.univ_anon.find? univCid.anon, store.univ_meta.find? univCid.meta with
    | some univAnon, some univMeta => pure $ some ⟨ univAnon, univMeta ⟩
    | _, _ => pure none
  | .expr  exprCid => do
    let store := (← read).store
    match store.expr_anon.find? exprCid.anon, store.expr_meta.find? exprCid.meta with
    | some exprAnon, some exprMeta => pure $ some ⟨ exprAnon, exprMeta ⟩
    | _, _ => pure none
  | .const constCid => do
    let store := (← read).store
    match store.const_anon.find? constCid.anon, store.const_meta.find? constCid.meta with
    | some constAnon, some constMeta => pure $ some ⟨ constAnon, constMeta ⟩
    | _, _ => pure none

def StoreKey.find! (key : StoreKey A) : TranspileM A := do
  let some value ← StoreKey.find? key | throw $ .custom "Cannot find key in store"
  return value

/-- 
Return `List (Inductive × List Constructor × IntRecursor × List ExtRecursor)`
-/
def getMutualIndInfo (ind : Inductive) : 
    TranspileM $ List (Inductive × List Constructor × IntRecursor × List ExtRecursor) := do
  let store := (← read).store
  let map := (← read).map
  -- let cid : ConstCid := ← match cache.find? ind.name with
  --   | some (cid, _) => return cid
  --   | none => throw $ .notFoundInCache ind.name
  let cid : ConstCid ← match store.const_meta.toList.find?
      fun (_, meta) => meta.name == ind.name with
    | some (metaCid, _) => match store.consts.toList.find? fun ⟨_, meta⟩ =>
        metaCid == meta with
      | some cid => pure cid
      | none => throw $ .notFoundInStore ind.name
    | none => throw $ .notFoundInStore ind.name
  let blockCid : ConstCid := ← match ← StoreKey.find! $ .const cid with 
    | ⟨.inductiveProj indAnon, .inductiveProj indMeta⟩ => 
      return ⟨indAnon.block, indMeta.block⟩
    | _ => throw $ .custom "cid not found in store"
  match ← StoreKey.find! $ .const blockCid with 
  | ⟨.mutIndBlock blockAnon, .mutIndBlock blockMeta⟩ => 
    blockAnon.zip blockMeta |>.mapM fun (_, indMeta) => do
      let indName := indMeta.name.projᵣ
      let ctors := indMeta.ctors.map fun ctor => ctor.name.projᵣ
      let mut intR : Name := default
      let mut extRs : List Name := []
      for ⟨b, recr⟩ in indMeta.recrs do 
        match b with 
        | .intr => intR := recr.name.projᵣ 
        | .extr => extRs := recr.name.projᵣ :: extRs
      let ind : Inductive := ← match map.find? indName with
        | some (.inductive ind) => return ind 
        | some x => throw $ .invalidConstantKind x "inductive"
        | none => throw $ .notFoundInMap intR
      let ctors ← ctors.mapM fun ctor =>
        match map.find? ctor with
        | some (.constructor ctor) => return ctor 
        | some x => throw $ .invalidConstantKind x "constructor"
        | none => throw $ .notFoundInMap ctor
      let irecr : IntRecursor := ← match map.find? intR with
        | some (.intRecursor recr) => return recr 
        | some x => throw $ .invalidConstantKind x "internal recursor"
        | none => throw $ .notFoundInMap intR
      let erecrs ← extRs.mapM fun extR => 
        match map.find? extR with
        | some (.extRecursor extR) => return extR 
        | some x => throw $ .invalidConstantKind x "external recursor"
        | none => throw $ .notFoundInMap extR
      return (ind, ctors, irecr, erecrs)
  | _ => throw $ .custom "blockCid not found in store"

/-- Gets the list of definitions involved in the mutual block of a definition -/
def getMutualDefInfo (defn : Definition) : TranspileM $ List Definition := do
  let consts := (← read).pStore.consts
  defn.all.mapM fun constIdx =>
    match consts[constIdx]! with
    | .definition d => pure d
    | _ => throw $ .custom "Invalid constant type"

/-- 
  Telescopes Yatima lambda `fun (x₁ : α₁) (x₂ : α₂) .. => body` into `(body, [(x₁, α₁), (x₂, α₂), ..])`
  Telescopes pi type `(a₁ : α₁) → (a₂ : α₂) → .. → α` into `(α, [(a₁, α₁), (a₂, α₂), ..])` -/
def telescope (expr : Expr) : Expr × List (Name × Expr) :=
  match expr with 
    | .pi .. => telescopeAux expr [] true
    | .lam .. => telescopeAux expr [] false
    | _ => (expr, [])
where 
  telescopeAux (expr : Expr) (bindAcc : List (Name × Expr)) (pi? : Bool) : 
      Expr × List (Name × Expr) :=
    match expr, pi? with 
    | .pi _ name _ ty body, true => telescopeAux body ((name, ty) :: bindAcc) true
    | .lam _ name _ ty body, false => telescopeAux body ((name, ty) :: bindAcc) false
    | _, _ => (expr, bindAcc.reverse)

end Yatima.Transpiler

namespace List

def last! [Inhabited α] (l : List α) : α :=
  l.reverse.head!

def takeLast (xs : List α) (n : Nat) : List α := 
  (xs.reverse.take n).reverse

end List 

def Lean.Name.isHygenic : Name → Bool
  | str p s => if s == "_hyg" then true else p.isHygenic
  | num p _ => p.isHygenic
  | _       => false

