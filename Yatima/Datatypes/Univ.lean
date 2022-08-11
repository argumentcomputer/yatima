import Yatima.Datatypes.Cid
import Yatima.Datatypes.Name

namespace Yatima

namespace Ipld

abbrev Nameᵣ k := Split Unit Name k

abbrev LNat k := Split Nat Unit k

inductive Univ (k : Kind) where
  | zero
  | succ  : UnivCid k → Univ k
  | max   : UnivCid k → UnivCid k → Univ k
  | imax  : UnivCid k → UnivCid k → Univ k
  | var   : Nameᵣ k → LNat k → Univ k
  deriving BEq, Inhabited

def Univ.ctorName : Univ k → String
  | .zero .. => "zero"
  | .succ .. => "succ"
  | .max  .. => "max"
  | .imax .. => "imax"
  | .var  .. => "var"

end Ipld

inductive Univ where
  | zero
  | succ  : Univ → Univ
  | max   : Univ → Univ → Univ
  | imax  : Univ → Univ → Univ
  | var   : Name → Nat → Univ
  deriving BEq, Inhabited

-- Reduces as a `max` applied to two values: `max a 0 = max 0 a = a` and `max (succ a) (succ b) = succ (max a b)`.
-- It is assumed that `a` and `b` are already reduced
def reduceMax (a b : Univ) : Univ :=
  match a, b with
  | Univ.zero, _ => b
  | _, Univ.zero => a
  | Univ.succ a, Univ.succ b => Univ.succ (reduceMax a b)
  | _, _ => Univ.max a b

-- Reduces as an `imax` applied to two values.
-- It is assumed that `a` and `b` are already reduced
def reduceIMax (a b : Univ) : Univ :=
  match b with
  -- IMax(a, b) will reduce to 0 if b == 0
  | Univ.zero => Univ.zero
  -- IMax(a, b) will reduce as Max(a, b) if b == Succ(..)
  | Univ.succ _ => reduceMax a b
  -- Otherwise, IMax(a, b) is stuck, with a and b reduced
  | _ => Univ.imax a b

-- Reduce, or simplify, the universe levels to a normal form. Notice that universe levels with no free variables
-- always reduce to a number, i.e., a sequence of `succ`s followed by a `zero`
def reduce (u : Univ) : Univ :=
  match u with
  | Univ.succ u' => Univ.succ (reduce u')
  | Univ.max a b => reduceMax a b
  | Univ.imax a b =>
    let b_prime := reduce b
    match b_prime with
    | Univ.zero => Univ.zero
    | Univ.succ _ => reduceMax (reduce a) b_prime
    | _ => Univ.imax (reduce a) b_prime
  | _ => u

-- Instantiate a variable and reduce at the same time. Assumes an already reduced `subst`. This function is only
-- used in the comparison algorithm, and it doesn't shift variables, because we want to instantiate a variable
-- `var idx` with `succ (var idx)`, so by shifting the variables we would transform `var (idx+1)` into `var idx`
-- which is not what we want
def instReduce (u : Univ) (idx : Nat) (subst : Univ) : Univ :=
  match u with
  | Univ.succ u => Univ.succ (instReduce u idx subst)
  | Univ.max a b => reduceMax (instReduce a idx subst) (instReduce b idx subst)
  | Univ.imax a b =>
    let b_prime := instReduce b idx subst
    match b_prime with
    | Univ.zero => Univ.zero
    | Univ.succ _ => reduceMax (instReduce a idx subst) b_prime
    | _ => Univ.imax (instReduce a idx subst) b_prime
  | Univ.var _ idx' => if idx' == idx then subst else u
  | Univ.zero => u

-- Instantiate multiple variables at the same time and reduce. Assumes already
-- reduced `substs`
def instBulkReduce (substs : List Univ) (u : Univ) : Univ :=
  match u with
  | Univ.succ u => Univ.succ (instBulkReduce substs u)
  | Univ.max a b => reduceMax (instBulkReduce substs a) (instBulkReduce substs b)
  | Univ.imax a b =>
    let b_prime := instBulkReduce substs b
    match b_prime with
    | Univ.zero => Univ.zero
    | Univ.succ _ => reduceMax (instBulkReduce substs a) b_prime
    | _ => Univ.imax (instBulkReduce substs a) b_prime
  | Univ.var nam idx =>
    match List.get? substs idx with
    | some u => u
    -- TODO: It is still unclear, at this point, whether we should shift or
    -- not the other variables. In fact, it is still unclear whether
    -- this case could happen at all. It would appear that the `substs`
    -- variable is a complete environment for the free variables
    -- inside `univ`
    | none => Univ.var nam (idx - List.length substs)
  | Univ.zero => u


--- Equality
-- We say that two universe levels `a` and `b` are (semantically) equal, if they
-- are equal as numbers for all possible substitution of free variables to
-- numbers. Although writing an algorithm that follows this exact scheme is
-- impossible, it is possible to write one that is equivalent to such semantical
-- equality.

-- Comparison algorithm `a <= b + diff`. Assumes `a` and `b` are already reduced
partial def leqUniv (a b : Univ) (diff : Int) : Bool :=
  if diff >= 0 && a == Univ.zero then true
  else match a, b with
  | Univ.zero, Univ.zero => diff >= 0
  | Univ.var _ _, Univ.zero => false
  | Univ.zero, Univ.var _ _ => diff >= 0
  | Univ.var _ x, Univ.var _ y => x == y && diff >= 0
  --! Succ cases
  | Univ.succ a, _ => leqUniv a b (diff - 1)
  | _, Univ.succ b => leqUniv a b (diff + 1)
  --! Max cases
  | Univ.max c d, _ => leqUniv c b diff && leqUniv d b diff
  | _, Univ.max c d => leqUniv a c diff || leqUniv a d diff
  --! IMax cases
  -- The case `a = imax c d` has only three possibilities:
  -- 1) d = var ..
  -- 2) d = max ..
  -- 3) d = imax ..
  -- It can't be any otherway since we are assuming `a` is reduced, and thus `d` is reduced as well
  | Univ.imax _ (Univ.var nam idx), _ =>
    -- In the case for `var idx`, we need to compare two substitutions:
    -- 1) idx <- zero
    -- 2) idx <- succ (var idx)
    -- In the first substitution, we know `a` becomes `zero`
    leqUniv Univ.zero (instReduce b idx Univ.zero) diff &&
    let succ := Univ.succ (Univ.var nam idx)
    leqUniv (instReduce a idx succ) (instReduce b idx succ) diff
  | Univ.imax c (Univ.max e f), _ =>
    -- Here we use the relationship
    -- imax c (max e f) = max (imax c e) (imax c f)
    let new_max := Univ.max (Univ.imax c e) (Univ.imax c f)
    leqUniv new_max b diff
  | Univ.imax c (Univ.imax e f), _ =>
    -- Here we use the relationship
    -- imax c (imax e f) = max (imax c e) (imax e f)
    let new_max := Univ.max (Univ.imax c e) (Univ.imax e f)
    leqUniv new_max b diff
  -- Analogous to previous case
  | _, Univ.imax _ (Univ.var nam idx) =>
    leqUniv (instReduce a idx Univ.zero) Univ.zero diff &&
    let succ := Univ.succ (Univ.var nam idx)
    leqUniv (instReduce a idx succ) (instReduce b idx succ) diff
  | _, Univ.imax c (Univ.max e f) =>
    let new_max := Univ.max (Univ.imax c e) (Univ.imax c f)
    leqUniv a new_max diff
  | _, Univ.imax c (Univ.imax e f) =>
    let new_max := Univ.max (Univ.imax c e) (Univ.imax e f)
    leqUniv a new_max diff
  | _, _ => panic! "Impossible case"

-- The equality algorithm. Assumes `a` and `b` are already reduced
partial def equalUniv (a b : Univ) : Bool :=
  leqUniv a b 0 && leqUniv b a 0

def equalUnivs (us us' : List Univ) : Bool :=
  match us, us' with
  | [], [] => true
  | u::us, u'::us' => equalUniv u u' && equalUnivs us us'
  | _, _ => false

-- Faster equality for zero, assumes reduced `a`
def univIsZero (a : Univ) : Bool :=
  match a with
  | .zero => true
  -- all other cases are false since they are either `Succ` or a reduced expression with free variables,
  -- which are never semantically equal to zero
  | _ => false

end Yatima
