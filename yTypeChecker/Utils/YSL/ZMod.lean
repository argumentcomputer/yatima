prelude
import yTypeChecker.Utils.YSL.Nat
import yTypeChecker.Utils.YSL.Int
import yTypeChecker.Utils.YSL.Ring

structure Zmod (_ : Nat) where
  rep : Int

namespace Zmod

instance : Coe Int (Zmod n) where
  coe i := .mk (i % n)

instance : Coe Nat (Zmod n) where
  coe i := .mk (i % n)

open Int

instance : Add (Zmod n) where
  add (a b : Zmod n) := (rep a + rep b) % (n : Int)

instance : Mul (Zmod n) where
  mul (a b : Zmod n) := (rep a * rep b) % (n : Int)

instance : Inhabited (Zmod n) where
  default := .mk 0

instance {n m : Nat} : OfNat (Zmod n) m where
  ofNat := m

instance : Pow (Zmod n) Nat where
  pow a l := Zmod.mk $ Nat.powMod n (natAbs ∘ Zmod.rep $ a) l

instance : Sub (Zmod n) where
  sub (a b : Zmod n) := (rep a - rep b) % (n : Int)

def modInv (a : Zmod n) : Zmod n := Int.modInv a.rep n

instance : Div (Zmod n) where
  div a b := a * modInv b

instance : HShiftRight (Zmod n) Nat (Zmod n) where
  hShiftRight x k := (x.rep.toNat.shiftRight k) % n

def norm (x : Zmod n) : Nat :=
  let rep := x.rep
  if rep < 0 then (rep - (rep / n - 1) * n).toNat else rep.toNat % n

instance : BEq (Zmod n) where
  beq x y := x.norm == y.norm

instance : Repr (Zmod n) where
  reprPrec n _ := s!"0x{Nat.toDigits 16 (Zmod.norm n) |>.asString}"

def modSqrt (a : Zmod n) : Option (Zmod n) :=
  let a' := natAbs ∘ Zmod.rep $ a
  match Nat.tonelli a' n with
    | some (_,y) => some ∘ Zmod.mk $ y
    | none => none

instance zmodField : Field (Zmod n) where
  inv := modInv

instance : ToString (Zmod n) where
  toString := reprStr

end Zmod
