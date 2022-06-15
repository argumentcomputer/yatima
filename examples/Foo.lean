-- inductive Bar
--   | hi | bye

-- def bar := Bar.hi

-- inductive MyNat
-- | zero : MyNat
-- | succ : MyNat → MyNat

mutual

  def QQQ : Nat → Nat
    | 0     => 0
    | n + 1 => 1 + WWW n
  
  def WWW : Nat → Nat
    | 0     => 0
    | n + 1 => 1 + QQQ n

end