import Yatima.Datatypes.Lurk
import Yatima.Datatypes.Const
import LightData

namespace Yatima

open Lurk

def _root_.Nat.toLDON : Nat → LDON
  | n => .num ⟨n⟩

instance : OfNat LDON n where
  ofNat := Nat.toLDON n

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

def TC.Univ.toLDON : TC.Univ → LDON
  | .zero     => (["Yatima.TC.Univ", 0] : List LDON)
  | .succ u   => (["Yatima.TC.Univ", 1, u.toLDON] : List LDON)
  | .max u v  => (["Yatima.TC.Univ", 2, u.toLDON, v.toLDON] : List LDON)
  | .imax u v => (["Yatima.TC.Univ", 3, u.toLDON, v.toLDON] : List LDON)
  | .var n    => (["Yatima.TC.Univ", 4, n.toLDON] : List LDON)
  
instance : Coe TC.Univ LDON where
  coe := TC.Univ.toLDON

def TC.Expr.toLDON : TC.Expr → LDON
  | .var n          => (["Yatima.TC.Expr", 0, n.toLDON] : List LDON)
  | .sort u         => (["Yatima.TC.Expr", 1, u] : List LDON)
  | .const ptr lvls => (["Yatima.TC.Expr", 2, ptr, lvls.map TC.Univ.toLDON] : List LDON)
  | .app fn arg     => (["Yatima.TC.Expr", 3, fn.toLDON, arg.toLDON] : List LDON)
  | .lam name body  => (["Yatima.TC.Expr", 4, name.toLDON, body.toLDON] : List LDON)
  | .pi x y         => (["Yatima.TC.Expr", 5, x.toLDON, y.toLDON] : List LDON)
  | .letE x y z     => (["Yatima.TC.Expr", 6, x.toLDON, y.toLDON, z.toLDON] : List LDON)
  | .lit l          => (["Yatima.TC.Expr", 7, l] : List LDON)
  | .proj n e       => (["Yatima.TC.Expr", 8, n.toLDON, e.toLDON] : List LDON)
  
instance : Coe TC.Expr LDON where
  coe := TC.Expr.toLDON

def TC.Axiom.toLDON : TC.Axiom → LDON
  | ⟨lvls, type, safe⟩ => (["Yatima.TC.Axiom", 0, lvls.toLDON, type, safe] : List LDON)

instance : Coe TC.Axiom LDON where
  coe := TC.Axiom.toLDON

def TC.Theorem.toLDON : TC.Theorem → LDON
  | ⟨lvls, type, value⟩ => (["Yatima.TC.Theorem", 0, lvls.toLDON, type, value] : List LDON)

instance : Coe TC.Theorem LDON where
  coe := TC.Theorem.toLDON

def TC.Opaque.toLDON : TC.Opaque → LDON
  | ⟨lvls, type, value, safe⟩ => 
    (["Yatima.TC.Opaque", 0, lvls.toLDON, type, value, safe] : List LDON)

instance : Coe TC.Opaque LDON where
  coe := TC.Opaque.toLDON

instance : Coe Lean.QuotKind LDON where coe
  | .type => (["Lean.QuotKind", 0] : List LDON)
  | .ctor => (["Lean.QuotKind", 1] : List LDON)
  | .lift => (["Lean.QuotKind", 2] : List LDON)
  | .ind  => (["Lean.QuotKind", 3] : List LDON)

def TC.Quotient.toLDON : TC.Quotient → LDON
  | ⟨lvls, type, kind⟩ => (["Yatima.TC.Quotient", 0, lvls.toLDON, type, kind] : List LDON)

instance : Coe TC.Quotient LDON where
  coe := TC.Quotient.toLDON

instance : Coe Lean.DefinitionSafety LDON where coe
  | .unsafe  => (["Lean.DefinitionSafety", 0] : List LDON)
  | .safe    => (["Lean.DefinitionSafety", 1] : List LDON)
  | .partial => (["Lean.DefinitionSafety", 2] : List LDON)

def TC.Definition.toLDON : TC.Definition → LDON
  | ⟨lvls, type, value, safety, all⟩ => 
    (["Yatima.TC.Definition", 0, lvls.toLDON, type, value, safety, all.map LDON.num] : List LDON)

instance : Coe TC.Definition LDON where
  coe := TC.Definition.toLDON

def TC.Constructor.toLDON : TC.Constructor → LDON
  | ⟨lvls, type, idx, params, fields, safe⟩ => 
    (["Yatima.TC.Constructor", 0, lvls.toLDON, type, idx.toLDON, params.toLDON, fields.toLDON, safe] : List LDON)

instance : Coe TC.Constructor LDON where
  coe := TC.Constructor.toLDON

def TC.RecursorRule.toLDON : TC.RecursorRule → LDON
  | ⟨fields, rhs⟩ => (["Yatima.TC.REcursorRule", 0, fields.toLDON, rhs] : List LDON)

instance : Coe TC.RecursorRule LDON where
  coe := TC.RecursorRule.toLDON

def TC.Recursor.toLDON : TC.Recursor → LDON
  | ⟨lvls, type, params, indices, motives, minors, rules, isK, internal, ind, all⟩ =>
    (["Yatima.TC.Recursor", 0, lvls.toLDON, type, params.toLDON, indices.toLDON, motives.toLDON, minors.toLDON, rules.map RecursorRule.toLDON, isK, internal, ind, all.map LDON.num] : List LDON)

instance : Coe TC.Recursor LDON where
  coe := TC.Recursor.toLDON

def TC.Inductive.toLDON : TC.Inductive → LDON
  | ⟨lvls, type, params, indices, ctors, recrs, recr, safe, refl, struct, unit⟩ =>
    (["Yatima.TC.Inductive", 0, lvls.toLDON, type, params.toLDON, indices.toLDON, ctors.map Constructor.toLDON, recrs.map Recursor.toLDON, recr, safe, safe, refl, struct, unit] : List LDON)

instance : Coe TC.Inductive LDON where
  coe := TC.Inductive.toLDON

def TC.Const.toLDON : TC.Const → LDON
  | .axiom x       => (["Yatima.TC.Const", 0, x] : List LDON)
  | .theorem x     => (["Yatima.TC.Const", 1, x] : List LDON)
  | .opaque x      => (["Yatima.TC.Const", 2, x] : List LDON)
  | .quotient x    => (["Yatima.TC.Const", 3, x] : List LDON)
  | .inductive x   => (["Yatima.TC.Const", 4, x] : List LDON)
  | .constructor x => (["Yatima.TC.Const", 5, x] : List LDON)
  | .recursor x    => (["Yatima.TC.Const", 6, x] : List LDON)
  | .definition x  => (["Yatima.TC.Const", 7, x] : List LDON)

end Yatima

