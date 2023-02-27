prelude
set_option linter.all false -- prevent error messages from runFrontend

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

theorem key : ∀ (n m : Nat), (∀ (n m : Nat), Eq n m) → Eq n m :=
  fun n m ih => (fun n m => ih n m) n m

--theorem key (p : Nat → Nat → Prop) : ∀ (n : Nat), (∀ (n m : Nat), p n m) → (m : Nat) → p n m :=
--  fun n ih m => (fun n m => ih n m) n m
