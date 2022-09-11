import Init.SimpLemmas

def f : Nat -> Nat
| _ => 1

theorem add_zero_id : ∀ (n: Nat), 0 + n = n
| 0 => rfl
| n+1 => congrArg Nat.succ (add_zero_id n)

