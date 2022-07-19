mutual

  def A : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + C n + 1

  def C : Nat → Nat
  | 0 => 0
  | n + 1 => B n + F n + A n + 1

  def E : Nat → Nat
  | 0 => 0
  | n + 1 => B n + A n + F n + 1

  def F : Nat → Nat
  | 0 => 0
  | n + 1 => B n + C n + E n + 1

  def B : Nat → Nat
  | 0 => 0
  | n + 1 => C n + 2

  def G : Nat → Nat 
  | 0 => 0
  | n + 1 => B n + F n + H n + 2

  def H : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + G n + 2

end

mutual

  def A' : Nat → Nat
  | 0 => 0
  | n + 1 => B' n + E' n + C' n + 1

  def C' : Nat → Nat
  | 0 => 0
  | n + 1 => B' n + F' n + A' n + 1

  def E' : Nat → Nat
  | 0 => 0
  | n + 1 => B' n + A' n + F' n + 1

  def F' : Nat → Nat
  | 0 => 0
  | n + 1 => B' n + C' n + E' n + 1

  def B' : Nat → Nat
  | 0 => 0
  | n + 1 => C' n + 2

  def G' : Nat → Nat
  | 0 => 0
  | n + 1 => B' n + F' n + H' n + 2

  def H' : Nat → Nat
  | 0 => 0
  | n + 1 => B' n + E' n + G' n + 2

end

mutual
  def I : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + G n + 2
end

def I' : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + G n + 2
