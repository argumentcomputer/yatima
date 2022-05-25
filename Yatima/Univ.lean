import Yatima.Cid
import Yatima.Name

namespace Yatima

inductive Univ where
  | zero
  | succ  : UnivCid → Univ
  | max   : UnivCid → UnivCid → Univ
  | imax  : UnivCid → UnivCid → Univ
  | param : Name → Nat → Univ
  deriving BEq, Inhabited

inductive UnivAnon where
  | zero
  | succ  : UnivAnonCid → UnivAnon
  | max   : UnivAnonCid → UnivAnonCid → UnivAnon
  | imax  : UnivAnonCid → UnivAnonCid → UnivAnon
  | param : Nat → UnivAnon
  deriving BEq, Inhabited

inductive UnivMeta where
  | zero
  | succ  : UnivMetaCid → UnivMeta
  | max   : UnivMetaCid → UnivMetaCid → UnivMeta
  | imax  : UnivMetaCid → UnivMetaCid → UnivMeta
  | param : Name → UnivMeta
  deriving BEq, Inhabited

def Univ.toAnon : Univ → UnivAnon
  | .zero      => .zero
  | .succ u    => .succ u.anon
  | .max a b   => .max a.anon b.anon
  | .imax a b  => .imax a.anon b.anon
  | .param _ i => .param i

def Univ.toMeta : Univ → UnivMeta
  | .zero      => .zero
  | .succ u    => .succ u.meta
  | .max a b   => .max a.meta b.meta
  | .imax a b  => .imax a.meta b.meta
  | .param n _ => .param n

-- namespace Univ

-- def instantiate (u : Univ) (i : Nat) (subst : Univ) : Univ :=
--   match u with
--   | succ  u   => succ (u.instantiate i subst)
--   | max   a b => max  (a.instantiate i subst) (b.instantiate i subst)
--   | imax  a b => imax (a.instantiate i subst) (b.instantiate i subst)
--   | param n i'  => if i' < i then u else if i' > i then param n (i' - 1) else subst
--   | zero      => u

-- def instantiateBulk (u : Univ) (substs : List Univ) : Univ :=
--   match u with
--   | succ  u   => succ (u.instantiateBulk substs)
--   | max   a b => max  (a.instantiateBulk substs) (b.instantiateBulk substs)
--   | imax  a b => imax (a.instantiateBulk substs) (b.instantiateBulk substs)
--   | param n i   =>
--     match substs.get? i with
--     | some u => u
--     | none   => param n (i - substs.length)
--   | zero => u

-- def combining (a b : Univ) : Univ :=
--   match a, b with
--   | zero, _ => b
--   | _, zero => a
--   | succ a, succ b => succ (a.combining b)
--   | _, _ => max a b

-- def simplify (u : Univ) : Univ :=
--   match u with
--   | succ u'  => succ (u'.simplify)
--   | max a b  => max (a.simplify) (b.simplify)
--   | imax a b =>
--     let b := b.simplify
--     match b with
--     | zero   => zero
--     | succ _ => a.simplify.combining b
--     | _      => imax a.simplify b
--   | _ => u

-- partial def leqCore (a b : Univ) (diff : Int) : Bool :=
--   if a == b && diff >= 0 then true
--   else match a, b with
--   | zero, zero => diff >= 0
--   | param _ x, param _ y => x == y && diff >= 0
--   | zero, param _ _ => diff >= 0
--   | param _ _, zero => false
--   | succ a, _ => leqCore a b (diff - 1)
--   | _, succ b => leqCore a b (diff + 1)
--   | max a₁ a₂, b => leqCore a₁ b diff && leqCore a₂ b diff
--   | a, max b₁ b₂ => leqCore a b₁ diff || leqCore a b₂ diff
--   | imax _ (param n idx), _ =>
--     let succ := succ (param n idx)
--     leqCore (a.instantiate idx zero) (b.instantiate idx zero) diff &&
--       leqCore (a.instantiate idx succ) (b.instantiate idx succ) diff
--   | _, imax _ (param n idx) =>
--     let succ' := succ (param n idx)
--     leqCore (a.instantiate idx zero) (b.instantiate idx zero) diff &&
--       leqCore (a.instantiate idx succ') (b.instantiate idx succ') diff
--   | imax a₁ (max a₂ a₃), _  => leqCore (max (imax a₁ a₂) (imax a₁ a₃)) b diff
--   | imax a₁ (imax a₂ a₃), _ => leqCore (max (imax a₁ a₃) (imax a₂ a₃)) b diff
--   | _, imax b₁ (max b₂ b₃)  => leqCore a (max (imax b₁ b₂) (imax b₁ b₃)) diff
--   | _, imax b₁ (imax b₂ b₃) => leqCore a (max (imax b₁ b₃) (imax b₂ b₃)) diff
--   | _, _ => unreachable!

-- def equalUniv (u u' : Univ) : Bool :=
--   let u  := u.simplify
--   let u' := u'.simplify
--   u.leqCore u' 0 && u'.leqCore u 0

-- def equalUnivs : List Univ → List Univ → Bool
--   | [], [] => true
--   | u :: us, u' :: us' => u.equalUniv u' && equalUnivs us us'
--   | _, _ => false

-- def isZero : Univ → Bool
--   | zero      => true
--   | param _ _ => false
--   | succ  _   => false
--   | max   u v => u.isZero && v.isZero
--   | imax  _ u => u.isZero

-- end Univ

end Yatima

