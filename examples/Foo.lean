mutual
  unsafe def Y4 : Nat → Nat
  | 0 => 0
  | n + 1 => Z4 n + Y5 n + 1

  unsafe def Y5 : Nat → Nat
  | 0 => 0
  | n + 1 => Z4 n + Y4 n + 1

  unsafe def Z4 : Nat → Nat
  | 0 => 0
  | n + 1 => Y4 n + Z5 n + 1

  unsafe def Z5 : Nat → Nat
  | 0 => 0
  | n + 1 => Y4 n + Z4 n + 1
end 

mutual
  unsafe def N4 : Nat → Nat
  | 0 => 0
  | n + 1 => M4 n + N5 n + 1

  unsafe def N5 : Nat → Nat
  | 0 => 0
  | n + 1 => M4 n + N4 n + 1

  unsafe def M4 : Nat → Nat
  | 0 => 0
  | n + 1 => N4 n + M5 n + 1

  unsafe def M5 : Nat → Nat
  | 0 => 0
  | n + 1 => N4 n + M4 n + 1
end 


-- N4: bagcyb6egbqlcavb2gme63bopne7ng2qc5bkshlldraqgjh7b5zus7pwboyhckkle
--     bagcyb6egbqlcbfqm7hch3cb55pogrn7gkfpyfygyo3lz5otxemoa6bhxdlr3xvju