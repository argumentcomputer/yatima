namespace WellFounded

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

end WellFounded

namespace Unsafe

mutual

  -- ACEF are weakly equal
  unsafe def A : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + C n + 1

  unsafe def C : Nat → Nat
  | 0 => 0
  | n + 1 => B n + F n + A n + 1

  unsafe def E : Nat → Nat
  | 0 => 0
  | n + 1 => B n + A n + F n + 1

  unsafe def F : Nat → Nat
  | 0 => 0
  | n + 1 => B n + C n + E n + 1

  -- B is distinctly different from the others
  unsafe def B : Nat → Nat
  | 0 => 0
  | n + 1 => C n + 2

  -- should be an external mutual block that references into
  -- the above mutual block; GH should be weakly equal
  unsafe def G : Nat → Nat
  | 0 => 0
  | n + 1 => B n + F n + H n + 2

  unsafe def H : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + G n + 2

end

unsafe def I : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + G n + 2

end Unsafe

namespace Partial

mutual

  partial def A : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + C n + 1

  partial def C : Nat → Nat
  | 0 => 0
  | n + 1 => B n + F n + A n + 1

  partial def E : Nat → Nat
  | 0 => 0
  | n + 1 => B n + A n + F n + 1

  partial def F : Nat → Nat
  | 0 => 0
  | n + 1 => B n + C n + E n + 1

  partial def B : Nat → Nat
  | 0 => 0
  | n + 1 => C n + 2

  partial def G : Nat → Nat
  | 0 => 0
  | n + 1 => B n + F n + H n + 2

  partial def H : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + G n + 2

end

partial def I : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + G n + 2

end Partial
