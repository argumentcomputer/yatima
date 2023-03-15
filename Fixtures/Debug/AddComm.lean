theorem add_comm : ∀ (n m : Nat), n + m = m + n
  | n, 0   => Eq.symm (Nat.zero_add n)
  | n, m+1 => by
    have : Nat.succ (n + m) = Nat.succ (m + n) :=
      by apply congrArg; apply Nat.add_comm
    rw [Nat.succ_add m n]
    apply this
