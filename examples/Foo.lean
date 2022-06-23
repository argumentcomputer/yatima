namespace terrible
mutual
  def A : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + 1

  def B : Nat → Nat
  | 0 => 0
  | n + 1 => C n + 2
  
  def C : Nat → Nat
  | 0 => 0
  | n + 1 => B n + F n + 1
 
  def E : Nat → Nat 
  | 0 => 0 
  | n + 1 => 2 + B n + A n

  def F : Nat → Nat 
  | 0 => 0 
  | n + 1 => 2 + B n + C n
end

#eval C 10
end terrible
