import Yatima.Datatypes.Const
import Lurk.LDON

open Lurk

instance : Coe Nat LDON where
  coe := .num ∘ .ofNat

instance : OfNat LDON n where
  ofNat := .num (.ofNat n)

instance : Coe Bool LDON where coe
  | false => 0
  | true  => 1

instance : Coe String LDON where
  coe := .str

instance : Coe F LDON where
  coe := .num

instance : Coe (List LDON) LDON where
  coe xs := xs.foldr (init := .nil) .cons

instance : Coe Lean.Literal LDON where coe  
  | .natVal n => ([0, n] : List LDON)
  | .strVal s => ([1, s] : List LDON)

namespace Yatima.IR

def Univ.toLDON : Univ → LDON
  | .zero     => ([0] : List LDON)
  | .succ u   => ([1, u.toLDON] : List LDON)
  | .max u v  => ([2, u.toLDON, v.toLDON] : List LDON)
  | .imax u v => ([3, u.toLDON, v.toLDON] : List LDON)
  | .var n    => ([4, n] : List LDON)

instance : Coe Univ LDON where
  coe := Univ.toLDON

def Expr.toLDON : Expr → LDON
  | .var n lvls     => ([0, n, lvls.map IR.Univ.toLDON] : List LDON)
  | .sort u         => ([1, u] : List LDON)
  | .const ptr lvls => ([2, ptr, lvls.map IR.Univ.toLDON] : List LDON)
  | .app fn arg     => ([3, fn.toLDON, arg.toLDON] : List LDON)
  | .lam body       => ([4, body.toLDON] : List LDON)
  | .pi x y         => ([5, x.toLDON, y.toLDON] : List LDON)
  | .letE x y z     => ([6, x.toLDON, y.toLDON, z.toLDON] : List LDON)
  | .lit l          => ([7, l] : List LDON)
  | .proj n e       => ([8, n, e.toLDON] : List LDON)

instance : Coe Expr LDON where
  coe := Expr.toLDON

def Axiom.toLDON : Axiom → LDON
  | ⟨lvls, type⟩ => ([0, lvls, type] : List LDON)

instance : Coe Axiom LDON where
  coe := Axiom.toLDON

def Theorem.toLDON : Theorem → LDON
  | ⟨lvls, type, value⟩ => ([0, lvls, type, value] : List LDON)

instance : Coe Theorem LDON where
  coe := Theorem.toLDON

def Opaque.toLDON : Opaque → LDON
  | ⟨lvls, type, value⟩ => ([0, lvls, type, value] : List LDON)

instance : Coe Opaque LDON where
  coe := Opaque.toLDON

instance : Coe Lean.QuotKind LDON where coe
  | .type => ([0] : List LDON)
  | .ctor => ([1] : List LDON)
  | .lift => ([2] : List LDON)
  | .ind  => ([3] : List LDON)

def Quotient.toLDON : Quotient → LDON
  | ⟨lvls, type, kind⟩ => ([0, lvls, type, kind] : List LDON)

instance : Coe Quotient LDON where
  coe := Quotient.toLDON

instance : Coe Lean.DefinitionSafety LDON where coe
  | .unsafe  => ([0] : List LDON)
  | .safe    => ([1] : List LDON)
  | .partial => ([2] : List LDON)

def Definition.toLDON : Definition → LDON
  | ⟨lvls, type, value, part⟩ =>
    ([0, lvls, type, value, part] : List LDON)

instance : Coe Definition LDON where
  coe := Definition.toLDON

def Constructor.toLDON : Constructor → LDON
  | ⟨lvls, type, idx, params, fields⟩ => ([0, lvls, type, idx, params, fields] : List LDON)

instance : Coe Constructor LDON where
  coe := Constructor.toLDON

def RecursorRule.toLDON : RecursorRule → LDON
  | ⟨fields, rhs⟩ => ([0, fields, rhs] : List LDON)

instance : Coe RecursorRule LDON where
  coe := RecursorRule.toLDON

def Recursor.toLDON : Recursor → LDON
  | ⟨lvls, type, params, indices, motives, minors, rules, isK, internal⟩ =>
    ([0, lvls, type, params, indices, motives, minors, rules.map RecursorRule.toLDON, isK, internal] : List LDON)

instance : Coe Recursor LDON where
  coe := Recursor.toLDON

def Inductive.toLDON : Inductive → LDON
  | ⟨lvls, type, params, indices, ctors, recrs, recr, refl, struct, unit⟩ =>
    ([0, lvls, type, params, indices, ctors.map Constructor.toLDON, recrs.map Recursor.toLDON, recr, refl, struct, unit] : List LDON)

instance : Coe Inductive LDON where
  coe := Inductive.toLDON

def InductiveProj.toLDON : InductiveProj → LDON
  | ⟨block, idx⟩ => ([0, block, idx] : List LDON)

instance : Coe InductiveProj LDON where
  coe := InductiveProj.toLDON

def ConstructorProj.toLDON : ConstructorProj → LDON
  | ⟨block, idx, cidx⟩ => ([0, block, idx, cidx] : List LDON)

instance : Coe ConstructorProj LDON where
  coe := ConstructorProj.toLDON

def RecursorProj.toLDON : RecursorProj → LDON
  | ⟨block, idx, ridx⟩ => ([0, block, idx, ridx] : List LDON)

instance : Coe RecursorProj LDON where
  coe := RecursorProj.toLDON

def DefinitionProj.toLDON : DefinitionProj → LDON
  | ⟨block, idx⟩ => ([0, block, idx] : List LDON)

instance : Coe DefinitionProj LDON where
  coe := DefinitionProj.toLDON

def Const.toLDON : Const → LDON
  | .axiom x           => ([0, x] : List LDON)
  | .theorem x         => ([1, x] : List LDON)
  | .opaque x          => ([2, x] : List LDON)
  | .definition x      => ([3, x] : List LDON)
  | .quotient x        => ([4, x] : List LDON)
  | .inductiveProj x   => ([5, x] : List LDON)
  | .constructorProj x => ([6, x] : List LDON)
  | .recursorProj x    => ([7, x] : List LDON)
  | .definitionProj x  => ([8, x] : List LDON)
  | .mutDefBlock x     => ([9, x.map Definition.toLDON] : List LDON)
  | .mutIndBlock x     => ([10, x.map Inductive.toLDON] : List LDON)

end Yatima.IR
