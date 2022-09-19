def map := [1, 2]
def my_length : List Nat → Nat := 
  fun xs => @List.casesOn Nat (fun _ => Nat) xs 0 fun n _ => n + 1
def root := my_length map
