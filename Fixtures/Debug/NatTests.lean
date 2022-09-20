def map := [1, 2]
def my_length : List Nat → Nat :=
  fun xs => @List.casesOn Nat (fun _ => Nat) xs 0 fun n _ => n + 1
def length := my_length map
def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * (fac n)
def fac4 := fac 4
