import Yatima.Name

mutual
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

  unsafe def G : Nat → Nat 
  | 0 => 0
  | n + 1 => B n + F n + H n + 2

  unsafe def H : Nat → Nat 
  | 0 => 0
  | n + 1 => B n + E n + G n + 2
end 


-- A: bagcyb6egbqlcbb6kcu6vs3bema6tzlkeponxksunaj45aegt7i5ixaeh64ggg2wj
-- C: bagcyb6egbqlcbb6kcu6vs3bema6tzlkeponxksunaj45aegt7i5ixaeh64ggg2wj
-- F: bagcyb6egbqlcbb6kcu6vs3bema6tzlkeponxksunaj45aegt7i5ixaeh64ggg2wj
-- E: bagcyb6egbqlcbb6kcu6vs3bema6tzlkeponxksunaj45aegt7i5ixaeh64ggg2wj