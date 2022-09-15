import Lean

namespace Yatima

scoped notation "Name" => Lean.Name

scoped notation "BinderInfo" => Lean.BinderInfo

scoped notation "Literal" => Lean.Literal

scoped notation "DefinitionSafety" => Lean.DefinitionSafety

scoped notation "QuotKind" => Lean.QuotKind

instance : BEq QuotKind where beq
  | .type, .type => true
  | .ctor, .ctor => true
  | .ind,  .ind  => true
  | .lift, .lift => true
  | _, _ => false

end Yatima