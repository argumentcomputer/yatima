import Yatima.Transpiler.TranspileM

namespace Yatima.Transpiler

inductive StoreKey : Type → Type
  | univ  : Ipld.Both Ipld.UnivCid  → StoreKey (Ipld.Both Ipld.Univ)
  | expr  : Ipld.Both Ipld.ExprCid  → StoreKey (Ipld.Both Ipld.Expr)
  | const : Ipld.Both Ipld.ConstCid → StoreKey (Ipld.Both Ipld.Const)

def StoreKey.find? : (key : StoreKey A) → TranspileM (Option A)
  | .univ  univCid => do
    let store := (← read).state.store
    match store.univ_anon.find? univCid.anon, store.univ_meta.find? univCid.meta with
    | some univAnon, some univMeta => pure $ some ⟨ univAnon, univMeta ⟩
    | _, _ => pure none
  | .expr  exprCid => do
    let store := (← read).state.store
    match store.expr_anon.find? exprCid.anon, store.expr_meta.find? exprCid.meta with
    | some exprAnon, some exprMeta => pure $ some ⟨ exprAnon, exprMeta ⟩
    | _, _ => pure none
  | .const constCid => do
    let store := (← read).state.store
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
  let cache := (← read).state.cache
  let consts := (← read).state.pStore.consts
  let cid : ConstCid := ← match cache.find? ind.name with 
  | some (cid, _) => return cid
  | none => throw $ .notFoundInCache ind.name
  let blockCid : ConstCid := ← match ← StoreKey.find! $ .const cid with 
  | ⟨.inductiveProj indAnon, .inductiveProj indMeta⟩ => 
    return ⟨indAnon.block, indMeta.block⟩
  | _ => throw $ .custom "cid not found in store"
  match ← StoreKey.find! $ .const blockCid with 
  | ⟨.mutIndBlock blockAnon, .mutIndBlock blockMeta⟩ => 
    blockAnon.zip blockMeta |>.mapM fun (_, indMeta) => do 
      let indName := indMeta.name.projᵣ
      let ctors := indMeta.ctors.map fun ctor => ctor.name.projᵣ
      let mut intR : Name := `none
      let mut extRs : List Name := []
      for ⟨b, recr⟩ in indMeta.recrs do 
        match b with 
        | .intr => intR := recr.name.projᵣ 
        | .extr => extRs := recr.name.projᵣ :: extRs
      let ind : Inductive := ← match cache.find? indName with 
        | some (_, idx) => match consts[idx]! with 
          | .inductive ind => return ind 
          | x => throw $ .invalidConstantKind x "inductive"
        | none => throw $ .notFoundInCache intR
      let ctors ← ctors.mapM fun ctor => 
        match cache.find? ctor with 
        | some (_, idx) => match consts[idx]! with 
          | .constructor ctor => return ctor 
          | x => throw $ .invalidConstantKind x "constructor"
        | none => throw $ .notFoundInCache ctor
      let irecr : IntRecursor := ← match cache.find? intR with 
        | some (_, idx) => match consts[idx]! with 
          | .intRecursor recr => return recr 
          | x => throw $ .invalidConstantKind x "internal recursor"
        | none => throw $ .notFoundInCache intR
      let erecrs ← extRs.mapM fun extR => 
        match cache.find? extR with 
        | some (_, idx) => match consts[idx]! with 
          | .extRecursor extR => return extR 
          | x => throw $ .invalidConstantKind x "external recursor"
        | none => throw $ .notFoundInCache extR
      return (ind, ctors, irecr, erecrs)
  | _ => throw $ .custom "blockCid not found in store"

/-- Gets the list of definitions involved in the mutual block of a definition -/
def getMutualDefInfo (defn : Definition) : TranspileM $ List Definition := do
  let consts := (← read).state.pStore.consts
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

