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

#print N._unsafe_rec
end Test0