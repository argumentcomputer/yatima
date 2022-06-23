mutual
  unsafe def Y4 : Nat → Nat
  | 0 => 0
  | n + 1 => Z4 n + Y5 n + Y5 n + 1

  unsafe def Y5 : Nat → Nat
  | 0 => 0
  | n + 1 => Z4 n + Y4 n + Y4 n + 1

  unsafe def Z4 : Nat → Nat
  | 0 => 0
  | n + 1 => Y4 n + Z5 n + Z5 n + 2

  unsafe def Z5 : Nat → Nat
  | 0 => 0
  | n + 1 => Y4 n + Z4 n + Z4 n + 2
end 

-- N4: bagcyb6egbqlca4om5ee23kuyb6s5fmcv5cmp3rzbojecquqqjtmgzh7ue56lpcxe