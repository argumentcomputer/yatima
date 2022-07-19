mutual

  -- ACEF are weakly equal
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

  -- B is distinctly different from the others
  partial def B : Nat → Nat
  | 0 => 0
  | n + 1 => C n + 2

  -- should be an external mutual block that references into
  -- the above mutual block; GH should be weakly equal
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
