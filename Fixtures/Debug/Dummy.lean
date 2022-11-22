namespace Test

inductive Nat
| zero : Nat
| succ : Nat → Nat

def f : Nat → Nat
| .zero => .zero
| .succ n => .succ (.succ (f n))


end Test

def zzz : Test.Nat := Test.f (.succ (.succ .zero))
