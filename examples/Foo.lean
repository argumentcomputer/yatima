namespace terrible
mutual
  def A : Nat → Nat
  | 0 => 0
  | n + 1 => B n + C n + 1

  def B : Nat → Nat
  | 0 => 0
  | n + 1 => C n + 2
  
  def C : Nat → Nat
  | 0 => 0
  | n + 1 => B n + A n + 1
end
end terrible
