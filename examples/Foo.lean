
-- inductive Bar
--   | hi | bye

-- def bar := Bar.hi

-- inductive MyNat
-- | zero : MyNat
-- | succ : MyNat → MyNat

mutual

  def a : Nat → Nat
    | 0     => 0
    | n + 1 => 1 + b n
  
  def b : Nat → Nat
    | 0     => 0
    | n + 1 => 1 + a n

end

mutual

  def WWW : Nat → Nat
    | 0     => 0
    | n + 1 => 1 + a n + QQQ n
  
  def QQQ : Nat → Nat
    | 0     => 0
    | n + 1 => 1 + b n + WWW n

end
