def Nat.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * n.factorial

def natFac := Nat.factorial 10

@[noinline] def mydiv (n m : Nat) := n / m
def natDiv := mydiv 3 3

@[noinline] def mymod (n m : Nat) := n % m
def natMod := mymod 0 3

#eval natMod

@[noinline] def myand (x y : Bool) := and x y
def myandtt := myand true true
def myandtf := myand true false
def myandft := myand false true
def myandff := myand false false

@[noinline] def lland (n m : Nat) := n.land m
def natLand := lland 20 17

#eval natLand