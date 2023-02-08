import Yatima.Datatypes.Lurk
import Yatima.Datatypes.Const

open Lurk

def Nat.toLDON : Nat → LDON
  | n => .num (.ofNat n)

namespace Yatima.TC

instance : OfNat LDON n where
  ofNat := .num (.ofNat n)

instance : Coe String LDON where
  coe := .str

instance : Coe F LDON where
  coe := .num

instance : Coe Lean.Literal LDON where coe
  | .strVal s => s
  | .natVal n => n.toLDON

instance : Coe (List LDON) LDON where
  coe xs := xs.foldr (init := .sym "NIL") .cons

instance : Coe Bool LDON where coe
  | false => (["Bool", 0] : List LDON)
  | true  => (["Bool", 1] : List LDON)

instance [Coe α LDON] : Coe (Option α) LDON where coe
  | some a => (["Option", 0, a] : List LDON)
  | none => (["Option", 1] : List LDON)

def Univ.toLDON : Univ → LDON
  | .zero     => (["Yatima.TC.Univ", 0] : List LDON)
  | .succ u   => (["Yatima.TC.Univ", 1, u.toLDON] : List LDON)
  | .max u v  => (["Yatima.TC.Univ", 2, u.toLDON, v.toLDON] : List LDON)
  | .imax u v => (["Yatima.TC.Univ", 3, u.toLDON, v.toLDON] : List LDON)
  | .var n    => (["Yatima.TC.Univ", 4, n.toLDON] : List LDON)

instance : Coe Univ LDON where
  coe := Univ.toLDON

def Expr.toLDON : Expr → LDON
  | .var n lvls     => (["Yatima.TC.Expr", 0, n.toLDON, lvls.map TC.Univ.toLDON] : List LDON)
  | .sort u         => (["Yatima.TC.Expr", 1, u] : List LDON)
  | .const ptr lvls => (["Yatima.TC.Expr", 2, ptr, lvls.map TC.Univ.toLDON] : List LDON)
  | .app fn arg     => (["Yatima.TC.Expr", 3, fn.toLDON, arg.toLDON] : List LDON)
  | .lam name body  => (["Yatima.TC.Expr", 4, name.toLDON, body.toLDON] : List LDON)
  | .pi x y         => (["Yatima.TC.Expr", 5, x.toLDON, y.toLDON] : List LDON)
  | .letE x y z     => (["Yatima.TC.Expr", 6, x.toLDON, y.toLDON, z.toLDON] : List LDON)
  | .lit l          => (["Yatima.TC.Expr", 7, l] : List LDON)
  | .proj n e       => (["Yatima.TC.Expr", 8, n.toLDON, e.toLDON] : List LDON)

instance : Coe Expr LDON where
  coe := Expr.toLDON

def Axiom.toLDON : Axiom → LDON
  | ⟨lvls, type, safe⟩ => (["Yatima.TC.Axiom", 0, lvls.toLDON, type, safe] : List LDON)

instance : Coe Axiom LDON where
  coe := Axiom.toLDON

def Theorem.toLDON : Theorem → LDON
  | ⟨lvls, type, value⟩ => (["Yatima.TC.Theorem", 0, lvls.toLDON, type, value] : List LDON)

instance : Coe Theorem LDON where
  coe := Theorem.toLDON

def Opaque.toLDON : Opaque → LDON
  | ⟨lvls, type, value, safe⟩ =>
    (["Yatima.TC.Opaque", 0, lvls.toLDON, type, value, safe] : List LDON)

instance : Coe Opaque LDON where
  coe := Opaque.toLDON

instance : Coe Lean.QuotKind LDON where coe
  | .type => (["Lean.QuotKind", 0] : List LDON)
  | .ctor => (["Lean.QuotKind", 1] : List LDON)
  | .lift => (["Lean.QuotKind", 2] : List LDON)
  | .ind  => (["Lean.QuotKind", 3] : List LDON)

def Quotient.toLDON : Quotient → LDON
  | ⟨lvls, type, kind⟩ => (["Yatima.TC.Quotient", 0, lvls.toLDON, type, kind] : List LDON)

instance : Coe Quotient LDON where
  coe := Quotient.toLDON

instance : Coe Lean.DefinitionSafety LDON where coe
  | .unsafe  => (["Lean.DefinitionSafety", 0] : List LDON)
  | .safe    => (["Lean.DefinitionSafety", 1] : List LDON)
  | .partial => (["Lean.DefinitionSafety", 2] : List LDON)

def Definition.toLDON : Definition → LDON
  | ⟨lvls, type, value, safety⟩ =>
    (["Yatima.TC.Definition", 0, lvls.toLDON, type, value, safety] : List LDON)

instance : Coe Definition LDON where
  coe := Definition.toLDON

def Constructor.toLDON : Constructor → LDON
  | ⟨lvls, type, idx, params, fields, safe⟩ =>
    (["Yatima.TC.Constructor", 0, lvls.toLDON, type, idx.toLDON, params.toLDON, fields.toLDON, safe] : List LDON)

instance : Coe Constructor LDON where
  coe := Constructor.toLDON

def RecursorRule.toLDON : RecursorRule → LDON
  | ⟨fields, rhs⟩ => (["Yatima.TC.RecursorRule", 0, fields.toLDON, rhs] : List LDON)

instance : Coe RecursorRule LDON where
  coe := RecursorRule.toLDON

def Recursor.toLDON : Recursor → LDON
  | ⟨lvls, type, params, indices, motives, minors, rules, isK, internal⟩ =>
    (["Yatima.TC.Recursor", 0, lvls.toLDON, type, params.toLDON, indices.toLDON, motives.toLDON, minors.toLDON, rules.map RecursorRule.toLDON, isK, internal] : List LDON)

instance : Coe Recursor LDON where
  coe := Recursor.toLDON

def Inductive.toLDON : Inductive → LDON
  | ⟨lvls, type, params, indices, ctors, recrs, recr, safe, refl, struct, unit⟩ =>
    (["Yatima.TC.Inductive", 0, lvls.toLDON, type, params.toLDON, indices.toLDON, ctors.map Constructor.toLDON, recrs.map Recursor.toLDON, recr, safe, safe, refl, struct, unit] : List LDON)

instance : Coe Inductive LDON where
  coe := Inductive.toLDON

def InductiveProj.toLDON : InductiveProj → LDON
  | ⟨block, idx⟩ =>
    (["Yatima.TC.InductiveProj", 0, block, idx.toLDON] : List LDON)

instance : Coe InductiveProj LDON where
  coe := InductiveProj.toLDON

def ConstructorProj.toLDON : ConstructorProj → LDON
  | ⟨block, idx, cidx⟩ =>
    (["Yatima.TC.ConstructorProj", 0, block, idx.toLDON, cidx.toLDON] : List LDON)

instance : Coe ConstructorProj LDON where
  coe := ConstructorProj.toLDON

def RecursorProj.toLDON : RecursorProj → LDON
  | ⟨block, idx, ridx⟩ =>
    (["Yatima.TC.RecursorProj", 0, block, idx.toLDON, ridx.toLDON] : List LDON)

instance : Coe RecursorProj LDON where
  coe := RecursorProj.toLDON

def DefinitionProj.toLDON : DefinitionProj → LDON
  | ⟨block, idx⟩ =>
    (["Yatima.TC.DefinitionProj", 0, block, idx.toLDON] : List LDON)

instance : Coe DefinitionProj LDON where
  coe := DefinitionProj.toLDON

def Const.toLDON : Const → LDON
  | .axiom x           => (["Yatima.TC.Const", 0, x] : List LDON)
  | .theorem x         => (["Yatima.TC.Const", 1, x] : List LDON)
  | .opaque x          => (["Yatima.TC.Const", 2, x] : List LDON)
  | .definition x      => (["Yatima.TC.Const", 3, x] : List LDON)
  | .quotient x        => (["Yatima.TC.Const", 4, x] : List LDON)
  | .inductiveProj x   => (["Yatima.TC.Const", 5, x] : List LDON)
  | .constructorProj x => (["Yatima.TC.Const", 6, x] : List LDON)
  | .recursorProj x    => (["Yatima.TC.Const", 7, x] : List LDON)
  | .definitionProj x  => (["Yatima.TC.Const", 8, x] : List LDON)
  | .mutDefBlock x     => (["Yatima.TC.Const", 9, x.map Definition.toLDON] : List LDON)
  | .mutIndBlock x     => (["Yatima.TC.Const", 10, x.map Inductive.toLDON] : List LDON)

end Yatima.TC
