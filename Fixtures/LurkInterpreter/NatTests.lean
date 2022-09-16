def isZero : Nat → Bool
  | 0 => true
  | n + 1 => false

def three : Nat := Nat.zero.succ.succ.succ
