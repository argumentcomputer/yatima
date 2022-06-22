-- prelude

-- def id (A : Type) (x : A) : A := x

-- inductive Unit where
-- | unit

inductive Bar
  | hi | bye

def bar := Bar.hi

inductive MyNat
| zero : MyNat
| succ : MyNat → MyNat
