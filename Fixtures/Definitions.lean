mutual
  -- ACEF are weakly equal
  unsafe def A : Nat → Nat
  | 0 => 0
  | n + 1 => B n + E n + C n + 1

  unsafe def C : Nat → Nat
  | 0 => 0
  | n + 1 => B n + F n + A n + 1

  unsafe def B : Nat → Nat
  | 0 => 0
  | n + 1 => C n + 2

  unsafe def E : Nat → Nat 
  | 0 => 0 
  | n + 1 => B n + A n + F n + 1

  unsafe def F : Nat → Nat 
  | 0 => 0 
  | n + 1 => B n + C n + E n + 1

  -- should be an external mutual block that references into
  -- the above mutual block; GH should be weakly equal
  unsafe def G : Nat → Nat 
  | 0 => 0
  | n + 1 => B n + F n + H n + 2

  unsafe def H : Nat → Nat 
  | 0 => 0
  | n + 1 => B n + E n + G n + 2
end 
