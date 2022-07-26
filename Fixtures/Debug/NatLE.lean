prelude 

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

inductive Nat.le (n : Nat) : Nat → Prop
  | refl     : Nat.le n n
  | step {m} : Nat.le n m → Nat.le n (succ m)
