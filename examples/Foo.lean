namespace Test0
mutual

  partial def D : Nat → Nat
  | 0     => 0
  | n + 1 => G n + D n + N n + 1

  partial def G : Nat → Nat
  | 0     => 0
  | n + 1 => O n + D n + G n + 3

  partial def I : Nat → Nat
  | 0     => 0
  | n + 1 => G n + D n + N n + 1

  partial def J : Nat → Nat
  | 0     => 0
  | n + 1 => J n + R n + 2

  partial def N : Nat → Nat
  | 0     => 0
  | n + 1 => J n + D n + 2

  partial def O : Nat → Nat
  | 0     => 0
  | n + 1 => N n + R n + 2

  partial def R : Nat → Nat
  | 0     => 0
  | n + 1 => G n + R n + N n + 1

end

  partial def T : Nat → Nat
  | 0     => 0
  | n + 1 => G n + T n + O n + 1

#print T._unsafe_rec
end Test0

-- [(0, [I, T, D, R]), (1, [J, N, O]), (2, [G])]
-- bagcyb6egbqlcadsnmcfwwzkkm2ih7se3gmhukhqiuhnwv2xb3crxkqe2q4pyfzsg
-- bagcyb6egbqlcadsnmcfwwzkkm2ih7se3gmhukhqiuhnwv2xb3crxkqe2q4pyfzsg

-- bagcyb6egbqlcbo46bdyn4ckfduo4tikzqibhtgnyc5qyurfsgqdzjpeq44zkpnjg
-- bagcyb6egbqlcbo46bdyn4ckfduo4tikzqibhtgnyc5qyurfsgqdzjpeq44zkpnjg

-- A: bagcyb6egbqlcbb6kcu6vs3bema6tzlkeponxksunaj45aegt7i5ixaeh64ggg2wj
-- C: bagcyb6egbqlcbb6kcu6vs3bema6tzlkeponxksunaj45aegt7i5ixaeh64ggg2wj
-- F: bagcyb6egbqlcbb6kcu6vs3bema6tzlkeponxksunaj45aegt7i5ixaeh64ggg2wj
-- E: bagcyb6egbqlcbb6kcu6vs3bema6tzlkeponxksunaj45aegt7i5ixaeh64ggg2wj