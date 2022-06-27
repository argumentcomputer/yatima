import Lean
import Yatima.ForStdLib
import Std

namespace Yatima.Compiler.Utils

open Lean

def compareNames : Name → Name → Ordering
  | .anonymous, .anonymous => .eq
  | .num namₗ nₗ _, .num namᵣ nᵣ _ =>
    if nₗ < nᵣ then .lt
    else
      if nₗ > nᵣ then .gt
      else compareNames namₗ namᵣ
  | .str namₗ sₗ _, .str namᵣ sᵣ _ =>
    if sₗ < sᵣ then .lt
    else
      if sₗ > sᵣ then .gt
      else compareNames namₗ namᵣ
  | .anonymous, .num .. => .lt
  | .anonymous, .str .. => .lt
  | .num .., .str .. => .lt
  | .num .., .anonymous => .gt
  | .str .., .anonymous => .gt
  | .str .., .num .. => .gt

instance : Ord Name where
  compare := compareNames

open YatimaStdLib (RBSet)

def getExprRefs : Expr → List Name 
  | .mdata _ exp _ => getExprRefs exp
  | .const name _ _ => [name]
  | .app func arg _ => 
    getExprRefs func ++  getExprRefs arg
  | .lam name type body _ => 
    getExprRefs type ++  getExprRefs body
  | .forallE name type body _ => 
    getExprRefs type ++  getExprRefs body
  | .letE  name type body exp _ => 
    getExprRefs type ++  getExprRefs body ++ getExprRefs exp
  | .proj name idx exp _ => getExprRefs exp
  | _ => []

def getConstRefs : ConstantInfo → List Name
  | .axiomInfo  val => getExprRefs val.type
  | .defnInfo   val => 
    getExprRefs val.type ++ getExprRefs val.value
  | .thmInfo    val => 
    getExprRefs val.type ++ getExprRefs val.value
  | .opaqueInfo val => 
    getExprRefs val.type ++ getExprRefs val.value
  | .ctorInfo   val => val.induct :: getExprRefs val.type
  | .inductInfo val => 
    getExprRefs val.type ++ val.all
  | .recInfo    val => 
    getExprRefs val.type ++ val.all ++ val.rules.map RecursorRule.ctor 
                ++ (val.rules.map (fun rule => getExprRefs rule.rhs)).join
  | .quotInfo   val => getExprRefs val.type

def getOpenReferencesInExpr (map : ConstMap) (mem : RBSet Name) :
    Expr → RBSet Name
  | .app e₁ e₂ .. =>
    getOpenReferencesInExpr map mem e₁ ⋃ₛ getOpenReferencesInExpr map mem e₂
  | .lam _ e₁ e₂ .. =>
    getOpenReferencesInExpr map mem e₁ ⋃ₛ getOpenReferencesInExpr map mem e₂
  | .forallE _ e₁ e₂ .. =>
    getOpenReferencesInExpr map mem e₁ ⋃ₛ getOpenReferencesInExpr map mem e₂
  | .letE _ e₁ e₂ e₃ .. =>
    getOpenReferencesInExpr map mem e₁
      ⋃ₛ getOpenReferencesInExpr map mem e₂
      ⋃ₛ getOpenReferencesInExpr map mem e₃
  | .mdata _ e ..  => getOpenReferencesInExpr map mem e
  | .proj n _ e .. =>
    getOpenReferencesInExpr map (if map.contains n then mem else mem.insert n) e
  | .const n .. => if map.contains n then mem else mem.insert n
  | _ => mem

def getOpenReferencesInConst (map : Lean.ConstMap) : Lean.ConstantInfo → RBSet Lean.Name
  | .axiomInfo struct => getOpenReferencesInExpr map .empty struct.type
  | .thmInfo struct =>
      getOpenReferencesInExpr
        map (getOpenReferencesInExpr map .empty struct.type) struct.value
  | .opaqueInfo struct =>
      getOpenReferencesInExpr
        map (getOpenReferencesInExpr map .empty struct.type) struct.value
  | .defnInfo struct =>
      getOpenReferencesInExpr
        map (getOpenReferencesInExpr map .empty struct.type) struct.value
  | .ctorInfo struct => getOpenReferencesInExpr map .empty struct.type
  | .inductInfo struct => getOpenReferencesInExpr map .empty struct.type
  | .recInfo struct =>
    struct.rules.foldl
      (init := getOpenReferencesInExpr map .empty struct.type)
      fun acc r => getOpenReferencesInExpr map acc r.rhs
  | .quotInfo struct => getOpenReferencesInExpr map .empty struct.type

def hasOpenReferenceInExpr (openReferences : RBSet Name) : Lean.Expr → Bool
  | .app e₁ e₂ .. =>
    hasOpenReferenceInExpr openReferences e₁
      || hasOpenReferenceInExpr openReferences e₂
  | .lam _ e₁ e₂ .. =>
    hasOpenReferenceInExpr openReferences e₁
      || hasOpenReferenceInExpr openReferences e₂
  | .forallE _ e₁ e₂ .. =>
    hasOpenReferenceInExpr openReferences e₁
      || hasOpenReferenceInExpr openReferences e₂
  | .letE _ e₁ e₂ e₃ .. =>
    hasOpenReferenceInExpr openReferences e₁
      || hasOpenReferenceInExpr openReferences e₂
      || hasOpenReferenceInExpr openReferences e₃
  | .mdata _ e ..  => hasOpenReferenceInExpr openReferences e
  | .proj n _ e .. =>
    openReferences.contains n
      || hasOpenReferenceInExpr openReferences e
  | .const n .. => openReferences.contains n
  | _ => false

def hasOpenReferenceInConst (openReferences : RBSet Name) :
    Lean.ConstantInfo → Bool
  | .axiomInfo struct => hasOpenReferenceInExpr openReferences struct.type
  | .thmInfo struct =>
    hasOpenReferenceInExpr openReferences struct.type
      || hasOpenReferenceInExpr openReferences struct.value
  | .opaqueInfo struct =>
    hasOpenReferenceInExpr openReferences struct.type
      || hasOpenReferenceInExpr openReferences struct.value
  | .defnInfo struct =>
    hasOpenReferenceInExpr openReferences struct.type
      || hasOpenReferenceInExpr openReferences struct.value
  | .ctorInfo struct => hasOpenReferenceInExpr openReferences struct.type
  | .inductInfo struct => hasOpenReferenceInExpr openReferences struct.type
  | .recInfo struct =>
    struct.rules.foldl
      (init := hasOpenReferenceInExpr openReferences struct.type)
      fun acc r => acc || hasOpenReferenceInExpr openReferences struct.type
  | .quotInfo struct => hasOpenReferenceInExpr openReferences struct.type

def filterConstants (cs : ConstMap) : ConstMap :=
  let openReferences : RBSet Name := cs.fold (init := .empty)
    fun acc _ c => acc ⋃ₛ getOpenReferencesInConst cs c
  Lean.List.toSMap $ cs.toList.filter fun (n, c) =>
    (!openReferences.contains n) && (!hasOpenReferenceInConst openReferences c)

instance : BEq ReducibilityHints where beq
  | .opaque,    .opaque    => true
  | .abbrev,    .abbrev    => true
  | .regular l, .regular r => l == r
  | _,          _          => false

instance : BEq QuotKind where beq
  | .type, .type => true
  | .ctor, .ctor => true
  | .lift, .lift => true
  | .ind,  .ind  => true
  | _,     _     => false

instance : BEq RecursorRule where beq
  | ⟨cₗ, nₗ, rₗ⟩, ⟨cᵣ, nᵣ, rᵣ⟩ => cₗ == cᵣ && nₗ == nᵣ && rₗ == rᵣ

instance : BEq ConstantInfo where
  beq (l r : ConstantInfo) : Bool :=
  l.name == r.name && l.levelParams == r.levelParams && l.type == r.type
    && match l, r with
  | .axiomInfo  l, .axiomInfo  r => l.isUnsafe == r.isUnsafe
  | .thmInfo    l, .thmInfo    r => l.value == r.value
  | .opaqueInfo l, .opaqueInfo r =>
    l.isUnsafe == r.isUnsafe && l.value == r.value
  | .defnInfo   l, .defnInfo   r =>
    l.value == r.value && l.safety == r.safety && l.hints == r.hints
  | .ctorInfo   l, .ctorInfo   r =>
    l.induct == r.induct && l.cidx == r.cidx && l.numParams == r.numParams
      && l.numFields == r.numFields && l.isUnsafe == r.isUnsafe
  | .inductInfo l, .inductInfo r =>
    l.numParams == r.numParams && l.numIndices == r.numIndices && l.all == r.all
      && l.ctors == r.ctors && l.isRec == r.isRec && l.isUnsafe == r.isUnsafe
      && l.isReflexive == r.isReflexive && l.isNested == r.isNested
  | .recInfo    l, .recInfo    r =>
    l.all == r.all && l.numParams == r.numParams && l.numIndices == r.numIndices
      && l.numMotives == r.numMotives && l.numMinors == r.numMinors
      && l.rules == r.rules && l.k == r.k && l.isUnsafe == r.isUnsafe
  | .quotInfo   l, .quotInfo   r => l.kind == r.kind
  | _, _ => false

end Yatima.Compiler.Utils
