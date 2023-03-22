import Yatima.Datatypes.Const
import Lurk.LDON

open Lurk

def Nat.toLDON : Nat → LDON
  | n => .num (.ofNat n)

namespace Yatima.IR

instance : OfNat LDON n where
  ofNat := .num (.ofNat n)

instance : Coe String LDON where
  coe := .str

instance : Coe F LDON where
  coe := .num

instance : Coe (List LDON) LDON where
  coe xs := xs.foldr (init := .nil) .cons

instance : Coe Lean.Literal LDON where coe
  | .natVal n => (["Lean.Literal", 0, n.toLDON] : List LDON)
  | .strVal s => (["Lean.Literal", 1, s] : List LDON)

instance : Coe Bool LDON where coe
  | false => (["Bool", 0] : List LDON)
  | true  => (["Bool", 1] : List LDON)

instance [Coe α LDON] : Coe (Option α) LDON where coe
  | some a => (["Option", 0, a] : List LDON)
  | none => (["Option", 1] : List LDON)

def Univ.toLDON : Univ → LDON
  | .zero     => (["Yatima.IR.Univ", 0] : List LDON)
  | .succ u   => (["Yatima.IR.Univ", 1, u.toLDON] : List LDON)
  | .max u v  => (["Yatima.IR.Univ", 2, u.toLDON, v.toLDON] : List LDON)
  | .imax u v => (["Yatima.IR.Univ", 3, u.toLDON, v.toLDON] : List LDON)
  | .var n    => (["Yatima.IR.Univ", 4, n.toLDON] : List LDON)

instance : Coe Univ LDON where
  coe := Univ.toLDON

def Expr.toLDON : Expr → LDON
  | .var n lvls     => (["Yatima.IR.Expr", 0, n.toLDON, lvls.map IR.Univ.toLDON] : List LDON)
  | .sort u         => (["Yatima.IR.Expr", 1, u] : List LDON)
  | .const ptr lvls => (["Yatima.IR.Expr", 2, ptr, lvls.map IR.Univ.toLDON] : List LDON)
  | .app fn arg     => (["Yatima.IR.Expr", 3, fn.toLDON, arg.toLDON] : List LDON)
  | .lam name body  => (["Yatima.IR.Expr", 4, name.toLDON, body.toLDON] : List LDON)
  | .pi x y         => (["Yatima.IR.Expr", 5, x.toLDON, y.toLDON] : List LDON)
  | .letE x y z     => (["Yatima.IR.Expr", 6, x.toLDON, y.toLDON, z.toLDON] : List LDON)
  | .lit l          => (["Yatima.IR.Expr", 7, l] : List LDON)
  | .proj n e       => (["Yatima.IR.Expr", 8, n.toLDON, e.toLDON] : List LDON)

instance : Coe Expr LDON where
  coe := Expr.toLDON

def Axiom.toLDON : Axiom → LDON
  | ⟨lvls, type⟩ => (["Yatima.IR.Axiom", 0, lvls.toLDON, type] : List LDON)

instance : Coe Axiom LDON where
  coe := Axiom.toLDON

def Theorem.toLDON : Theorem → LDON
  | ⟨lvls, type, value⟩ => (["Yatima.IR.Theorem", 0, lvls.toLDON, type, value] : List LDON)

instance : Coe Theorem LDON where
  coe := Theorem.toLDON

def Opaque.toLDON : Opaque → LDON
  | ⟨lvls, type, value⟩ =>
    (["Yatima.IR.Opaque", 0, lvls.toLDON, type, value] : List LDON)

instance : Coe Opaque LDON where
  coe := Opaque.toLDON

instance : Coe Lean.QuotKind LDON where coe
  | .type => (["Lean.QuotKind", 0] : List LDON)
  | .ctor => (["Lean.QuotKind", 1] : List LDON)
  | .lift => (["Lean.QuotKind", 2] : List LDON)
  | .ind  => (["Lean.QuotKind", 3] : List LDON)

def Quotient.toLDON : Quotient → LDON
  | ⟨lvls, type, kind⟩ => (["Yatima.IR.Quotient", 0, lvls.toLDON, type, kind] : List LDON)

instance : Coe Quotient LDON where
  coe := Quotient.toLDON

instance : Coe Lean.DefinitionSafety LDON where coe
  | .unsafe  => (["Lean.DefinitionSafety", 0] : List LDON)
  | .safe    => (["Lean.DefinitionSafety", 1] : List LDON)
  | .partial => (["Lean.DefinitionSafety", 2] : List LDON)

def Definition.toLDON : Definition → LDON
  | ⟨lvls, type, value, part⟩ =>
    (["Yatima.IR.Definition", 0, lvls.toLDON, type, value, part] : List LDON)

instance : Coe Definition LDON where
  coe := Definition.toLDON

def Constructor.toLDON : Constructor → LDON
  | ⟨lvls, type, idx, params, fields⟩ =>
    (["Yatima.IR.Constructor", 0, lvls.toLDON, type, idx.toLDON, params.toLDON, fields.toLDON] : List LDON)

instance : Coe Constructor LDON where
  coe := Constructor.toLDON

def RecursorRule.toLDON : RecursorRule → LDON
  | ⟨fields, rhs⟩ => (["Yatima.IR.RecursorRule", 0, fields.toLDON, rhs] : List LDON)

instance : Coe RecursorRule LDON where
  coe := RecursorRule.toLDON

def Recursor.toLDON : Recursor → LDON
  | ⟨lvls, type, params, indices, motives, minors, rules, isK, internal⟩ =>
    (["Yatima.IR.Recursor", 0, lvls.toLDON, type, params.toLDON, indices.toLDON, motives.toLDON, minors.toLDON, rules.map RecursorRule.toLDON, isK, internal] : List LDON)

instance : Coe Recursor LDON where
  coe := Recursor.toLDON

def Inductive.toLDON : Inductive → LDON
  | ⟨lvls, type, params, indices, ctors, recrs, recr, refl, struct, unit⟩ =>
    (["Yatima.IR.Inductive", 0, lvls.toLDON, type, params.toLDON, indices.toLDON, ctors.map Constructor.toLDON, recrs.map Recursor.toLDON, recr, refl, struct, unit] : List LDON)

instance : Coe Inductive LDON where
  coe := Inductive.toLDON

def InductiveProj.toLDON : InductiveProj → LDON
  | ⟨block, idx⟩ =>
    (["Yatima.IR.InductiveProj", 0, block, idx.toLDON] : List LDON)

instance : Coe InductiveProj LDON where
  coe := InductiveProj.toLDON

def ConstructorProj.toLDON : ConstructorProj → LDON
  | ⟨block, idx, cidx⟩ =>
    (["Yatima.IR.ConstructorProj", 0, block, idx.toLDON, cidx.toLDON] : List LDON)

instance : Coe ConstructorProj LDON where
  coe := ConstructorProj.toLDON

def RecursorProj.toLDON : RecursorProj → LDON
  | ⟨block, idx, ridx⟩ =>
    (["Yatima.IR.RecursorProj", 0, block, idx.toLDON, ridx.toLDON] : List LDON)

instance : Coe RecursorProj LDON where
  coe := RecursorProj.toLDON

def DefinitionProj.toLDON : DefinitionProj → LDON
  | ⟨block, idx⟩ =>
    (["Yatima.IR.DefinitionProj", 0, block, idx.toLDON] : List LDON)

instance : Coe DefinitionProj LDON where
  coe := DefinitionProj.toLDON

def Const.toLDON : Const → LDON
  | .axiom x           => (["Yatima.IR.Const", 0, x] : List LDON)
  | .theorem x         => (["Yatima.IR.Const", 1, x] : List LDON)
  | .opaque x          => (["Yatima.IR.Const", 2, x] : List LDON)
  | .definition x      => (["Yatima.IR.Const", 3, x] : List LDON)
  | .quotient x        => (["Yatima.IR.Const", 4, x] : List LDON)
  | .inductiveProj x   => (["Yatima.IR.Const", 5, x] : List LDON)
  | .constructorProj x => (["Yatima.IR.Const", 6, x] : List LDON)
  | .recursorProj x    => (["Yatima.IR.Const", 7, x] : List LDON)
  | .definitionProj x  => (["Yatima.IR.Const", 8, x] : List LDON)
  | .mutDefBlock x     => (["Yatima.IR.Const", 9, x.map Definition.toLDON] : List LDON)
  | .mutIndBlock x     => (["Yatima.IR.Const", 10, x.map Inductive.toLDON] : List LDON)

end Yatima.IR
