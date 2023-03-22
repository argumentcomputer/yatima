def id' : α → α := fun a => a

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit' : Sort u where
  | unit

abbrev Unit' : Type := PUnit

inductive Nat'
  | zero
  | succ : Nat' → Nat'

def natAdd : Nat → Nat → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)

theorem add_comm : ∀ (n m : Nat), n + m = m + n
  | n, 0   => Eq.symm (Nat.zero_add n)
  | n, m+1 => by
    have : Nat.succ (n + m) = Nat.succ (m + n) :=
      by apply congrArg; apply Nat.add_comm
    rw [Nat.succ_add m n]
    apply this
