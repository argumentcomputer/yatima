import Lean

namespace Yatima

scoped notation "Name" => Lean.Name

scoped notation "BinderInfo" => Lean.BinderInfo

scoped notation "Literal" => Lean.Literal

scoped notation "DefinitionSafety" => Lean.DefinitionSafety

scoped notation "QuotKind" => Lean.QuotKind

def compareNames : Name → Name → Ordering
  | .anonymous, .anonymous => .eq
  | .num namₗ nₗ, .num namᵣ nᵣ =>
    if nₗ < nᵣ then .lt
    else
      if nₗ > nᵣ then .gt
      else compareNames namₗ namᵣ
  | .str namₗ sₗ, .str namᵣ sᵣ =>
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

instance : BEq QuotKind where beq
  | .type, .type => true
  | .ctor, .ctor => true
  | .ind,  .ind  => true
  | .lift, .lift => true
  | _, _ => false

instance : BEq QuotKind where beq
  | .type, .type => true
  | .ctor, .ctor => true
  | .lift, .lift => true
  | .ind,  .ind  => true
  | _,     _     => false

instance : BEq Lean.ReducibilityHints where beq
  | .opaque,    .opaque    => true
  | .abbrev,    .abbrev    => true
  | .regular l, .regular r => l == r
  | _,          _          => false

instance : BEq Lean.RecursorRule where beq
  | ⟨cₗ, nₗ, rₗ⟩, ⟨cᵣ, nᵣ, rᵣ⟩ => cₗ == cᵣ && nₗ == nᵣ && rₗ == rᵣ

instance : BEq Lean.ConstantInfo where
  beq (l r : Lean.ConstantInfo) : Bool :=
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

end Yatima
