prelude

def id (a : α) (f : α → α → α) : α := f (f a a) a

inductive Nat
  | zero : Nat
  | succ : Nat → Nat

#check Nat.succ
/-
Expected output:

`Nat.zero`:
`[["Nat", 0], <mdata>]`

`Nat.succ`:
`lambda n, [["Nat", 1, n], <mdata>]`




-/