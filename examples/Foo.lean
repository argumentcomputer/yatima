-- mutual
--   def a : Nat → Nat
--     | 0     => 0
--     | n + 1 => 1 + b n

--   def b : Nat → Nat
--     | 0     => 0
--     | n + 1 => 1 + a n
-- end

-- mutual
--   partial def WWW : Nat → Nat
--     | 0     => 0
--     | n + 1 => 1 + a n + QQQ n

--   partial def QQQ : Nat → Nat
--     | 0     => 0
--     | n + 1 => 1 + b n + WWW n
-- end

-- #print QQQ._unsafe_rec

mutual 
  partial def A : Nat → Nat
  | 0 => 0
  | n + 1 => B n + 1

  partial def B : Nat → Nat
  | 0 => 0 
  | n + 1 => C n + 1

  partial def C : Nat → Nat
  | 0 => 0 
  | n + 1 => A n + 1
end


mutual 
  theorem hA : ∀ n, A._unsafe_rec n = n 
  | 0 => rfl 
  | n + 1 => 
    have h : A._unsafe_rec (n + 1) = B._unsafe_rec n + 1 := rfl 
    h ▸ (hB n).symm ▸ rfl

  theorem hB : ∀ n, B._unsafe_rec n = n
  | 0 => rfl 
  | n + 1 => 
    have h : B._unsafe_rec (n + 1) = C._unsafe_rec n + 1 := rfl 
    h ▸ (hC n).symm ▸ rfl

  theorem hC : ∀ n, C._unsafe_rec n = n
  | 0 => rfl 
  | n + 1 => 
    have h : C._unsafe_rec (n + 1) = A._unsafe_rec n + 1 := rfl 
    h ▸ (hA n).symm ▸ rfl
end 