import Lean
import Yatima.Ipld.Cid

namespace Yatima

/-- Reflects `Lean.Level` -/
inductive Univ where
  | zero
  | succ  : Univ → Univ
  | max   : Univ → Univ → Univ
  | imax  : Univ → Univ → Univ
  | param : Nat   → Univ
  deriving BEq, Inhabited

inductive LitType where
  | natTyp
  | strTyp
  deriving Inhabited, BEq

mutual

  inductive Expr
  | var   : Nat → Expr
  | sort  : Univ → Expr
  | const : Const → List Univ → Expr
  | app   : Expr → Expr → Expr
  | lam   : Expr → Expr → Expr
  | pi    : Expr → Expr → Expr
  | letE  : Expr → Expr → Expr → Expr
  | lit   : Lean.Literal → Expr
  | lty   : LitType → Expr
  | fix   : Expr → Expr
  deriving Inhabited

  inductive RecursorRule
  -- ctor, n_fields, rhs
  | mk : Cid → Nat → Expr → RecursorRule

  inductive Const
  -- cid, Univ, type
  | axiomC : Cid → Nat → Expr → Const

  -- Univ, value, type
  | theoremC : Nat → Expr → Expr → Const

  -- cid, Univ, value, type, is_unsafe
  | opaque : Cid → Nat → Expr → Expr → Bool → Const

  -- cid, Univ, value, type, safety
  | defn : Cid → Nat → Expr → Expr → Lean.DefinitionSafety → Const

  -- cid, Univ, type, ctor_idx, num_params, num_fields, is_unsafe
  | ctor : Cid → Nat → Expr → Nat → Nat → Nat → Bool → Const

  -- cid, Univ, type, num_params, num_indices, is_unit, is_rec, is_unsafe, is_reflexive, is_nested
  | induct : Cid → Nat → Expr → Nat → Nat → Bool → Bool → Bool → Bool → Bool → Const

  -- cid, Univ, type, num_params, num_indices, num_motives, num_minors, rules, k, is_unsafe
  | recursor : Cid → Nat → Expr → Nat → Nat → Nat → Nat → List RecursorRule → Bool → Bool → Const

  -- Univ, type, kind
  | quotient : Nat → Expr → Lean.QuotKind → Const

end

instance : Inhabited RecursorRule where
  default := RecursorRule.mk default default default

instance : Inhabited Const where
  default := Const.axiomC default default default

namespace Univ

def instantiate (u : Univ) (i : Nat) (subst : Univ) : Univ :=
  match u with
  | succ  u   => succ (u.instantiate i subst)
  | max   a b => max  (a.instantiate i subst) (b.instantiate i subst)
  | imax  a b => imax (a.instantiate i subst) (b.instantiate i subst)
  | param i'  => if i' < i then u else if i' > i then param (i' - 1) else subst
  | zero      => u

def instantiateBulk (u : Univ) (substs : List Univ) : Univ :=
  match u with
  | succ  u   => succ (u.instantiateBulk substs)
  | max   a b => max  (a.instantiateBulk substs) (b.instantiateBulk substs)
  | imax  a b => imax (a.instantiateBulk substs) (b.instantiateBulk substs)
  | param i   =>
    match substs.get? i with
    | some u => u
    | none   => param (i - substs.length)
  | zero => u

def combining (a b : Univ) : Univ :=
  match a, b with
  | zero, _ => b
  | _, zero => a
  | succ a, succ b => succ (a.combining b)
  | _, _ => max a b

def simplify (u : Univ) : Univ :=
  match u with
  | succ u'  => succ (u'.simplify)
  | max a b  => max (a.simplify) (b.simplify)
  | imax a b =>
    let b := b.simplify
    match b with
    | zero   => zero
    | succ _ => a.simplify.combining b
    | _      => imax a.simplify b
  | _ => u

partial def leqCore (a b : Univ) (diff : Int) : Bool :=
  if a == b && diff >= 0 then true
  else match a, b with
  | zero, zero => diff >= 0
  | param x, param y => x == y && diff >= 0
  | zero, param _ => diff >= 0
  | param _, zero => false
  | succ a, _ => leqCore a b (diff - 1)
  | _, succ b => leqCore a b (diff + 1)
  | max a₁ a₂, b => leqCore a₁ b diff && leqCore a₂ b diff
  | a, max b₁ b₂ => leqCore a b₁ diff || leqCore a b₂ diff
  | imax _ (param idx), _ =>
    let succ := succ (param idx)
    leqCore (a.instantiate idx zero) (b.instantiate idx zero) diff &&
      leqCore (a.instantiate idx succ) (b.instantiate idx succ) diff
  | _, imax _ (param idx) =>
    let succ' := succ (param idx)
    leqCore (a.instantiate idx zero) (b.instantiate idx zero) diff &&
      leqCore (a.instantiate idx succ') (b.instantiate idx succ') diff
  | imax a₁ (max a₂ a₃), _  => leqCore (max (imax a₁ a₂) (imax a₁ a₃)) b diff
  | imax a₁ (imax a₂ a₃), _ => leqCore (max (imax a₁ a₃) (imax a₂ a₃)) b diff
  | _, imax b₁ (max b₂ b₃)  => leqCore a (max (imax b₁ b₂) (imax b₁ b₃)) diff
  | _, imax b₁ (imax b₂ b₃) => leqCore a (max (imax b₁ b₃) (imax b₂ b₃)) diff
  | _, _ => unreachable!

def equalUniv (u u' : Univ) : Bool :=
  let u  := u.simplify
  let u' := u'.simplify
  u.leqCore u' 0 && u'.leqCore u 0

def equalUnivs : List Univ → List Univ → Bool
  | [], [] => true
  | u :: us, u' :: us' => u.equalUniv u' && equalUnivs us us'
  | _, _ => false

def isZero : Univ → Bool
  | zero      => true
  | param _   => false
  | succ  _   => false
  | max   u v => u.isZero && v.isZero
  | imax  _ u => u.isZero

end Univ

end Yatima
