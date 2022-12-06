
import Lean.Meta

open Lean Lean.Meta

deriving instance Inhabited for ConstantInfo -- required for Array.qsort

structure FindOptions where
  stage1       : Bool := true
  checkPrivate : Bool := false

def findCore (ϕ : ConstantInfo → MetaM Bool) (opts : FindOptions := {}) : MetaM (Array ConstantInfo) := do
  let ms ← if !opts.stage1 then 
    return #[] 
  else 
    (← getEnv).constants.map₁.foldM (init := #[]) check
  (← getEnv).constants.map₂.foldlM (init := ms) check

  where
    check ms name cinfo := do
      if opts.checkPrivate || (not $ isPrivateName name) then
        if (← ϕ cinfo) then pure (ms.push cinfo) else pure ms
      else pure ms

def find (ϕ : ConstantInfo → MetaM Bool) (opts : FindOptions := {}) : MetaM Unit := do
  let cinfos ← findCore ϕ opts
  let cinfos := cinfos.qsort (fun p q => p.name.lt q.name)
  for cinfo in cinfos do
    println! "{cinfo.name} : {← Meta.ppExpr cinfo.type}"

inductive WideTree where
| branch: (List WideTree) → WideTree
| leaf: WideTree

#eval find fun cinfo => return (``WideTree).isPrefixOf cinfo.name