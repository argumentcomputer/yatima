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

-- B, E, F, C, A
--XB, WE, ZA, YC, UF


-- [B, [E, F, C, A], [G, H]]
-- [c_0], ..., [n_0, ..., n_k], ..., [m_0, ..., m_j], ... [c_i]]
