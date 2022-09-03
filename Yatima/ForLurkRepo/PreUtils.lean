import YatimaStdLib.Algebra.Defs

/- Taken from mathlib, TODO: Give credit -/
namespace Nat 

/-- Helper function for the extended GCD algorithm (`nat.xgcd`). -/
partial def xgcdAux : Nat → Int → Int → Nat → Int → Int → Nat × Int × Int
| 0, _, _, r', s', t' => (r', s', t')
| r, s, t, r', s', t' =>
  -- have : r' % r < r := sorry
  let q := r' / r 
  xgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : Nat) : Int × Int := (xgcdAux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA (x y : Nat) : Int := (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB (x y : Nat) : Int := (xgcd x y).2

end Nat

namespace Int 

def modToNat : Int → Nat → Nat
  | .ofNat x,   n => x % n 
  | .negSucc x, n => n - x % n - 1

@[simp] theorem modToNat_ofNat : modToNat (ofNat a) n = a % n := rfl
@[simp] theorem modToNat_neghSucc : modToNat (negSucc a) n = n - a % n - 1 := rfl

#eval modToNat 7 0

theorem modToNat_le {n : Nat} : modToNat a n.succ < n.succ := by 
  cases a with 
  | ofNat x => 
    simp [Nat.mod_lt x (Nat.succ_pos n)]
  | negSucc x => 
    -- apply Nat.lt_trans _ _ _
    sorry

end Int 

namespace Fin 

def ofInt {n : Nat} (a : Int) : Fin n.succ := 
  ⟨Int.modToNat a n.succ, Int.modToNat_le⟩

/- TODO: This is copied from core since it is private -/
private theorem mlt {b : Nat} : {a : Nat} → a < n → b % n < n
  | 0,   h => Nat.mod_lt _ h
  | _+1, h =>
    have : n > 0 := Nat.lt_trans (Nat.zero_lt_succ _) h;
    Nat.mod_lt _ this

def inv : Fin n → Fin n
  | ⟨a, h⟩ => ⟨(Int.modToNat (Nat.gcdA a n) n) % n, mlt h⟩

instance : Inv (Fin n) where 
  inv a := Fin.inv a

end Fin 