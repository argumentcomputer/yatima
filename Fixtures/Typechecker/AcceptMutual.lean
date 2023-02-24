set_option linter.all false -- prevent error messages from runFrontend

mutual

  def A : Nat → Nat
  | 0 => 0
  | n + 1 => B n + C n + 1

  def C : Nat → Nat
  | 0 => 0
  | n + 1 => B n + A n + 1

  def B : Nat → Nat
  | 0 => 0
  | n + 1 => C n + 2

  def G : Nat → Nat
  | 0 => 0
  | n + 1 => B n + A n + H n + 2

  def H : Nat → Nat
  | 0 => 0
  | n + 1 => B n + C n + G n + 2

end
