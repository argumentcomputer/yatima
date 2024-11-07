prelude
import yTypeChecker.Init
import yTypeChecker.Utils.YSL.Nat

namespace Int

def gcdExtNat (a : Nat) (b : Nat) : Int × Int × Int :=
  match h : b with
    | 0 => (1, 0, a)
    | k + 1 =>
      let p := Nat.quotRem a b
      let q := p.1
      let r := p.2
      have : r < k.succ := by
        have h2 := k.succ_ne_zero
        rw [← h] at *
        apply Nat.mod_lt
        exact Nat.zero_lt_of_ne_zero h2
      let (s, t, g) := gcdExtNat b r
      (t, s - q * t, g)

def gcdExt (a : Int) (b : Int) : Int × Int × Int :=
  gcdExtNat (Int.natAbs a) (Int.natAbs b)

def modInv (a : Int) (m : Int) : Int :=
  let (i, _, g) := Int.gcdExt a m
  let mkPos (x : Int) := if x < 0 then x + m else x
  if g == 1 then mkPos i else 0
