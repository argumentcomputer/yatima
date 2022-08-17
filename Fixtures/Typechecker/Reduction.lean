def A  := (fun x => x) true
def A' := true

def B  := match false with
  | false => true
  | true => false
def B' := true

def C  := match true with
  | false => true
  | true => false
def C' := false

-- indexed inductive type
inductive Split (A : Type) (B : Type) : Bool → Type where
  | injₗ : A → Split A B true
  | injᵣ : B → Split A B false

def proj₁ (s : Split Nat Bool true) : Nat := s.casesOn (fun n => n) (fun _ => .zero)
def proj₂ (s : Split Nat Bool false) : Bool := s.casesOn (fun _ => false) (fun b => b)

def D  := proj₁ $ .injₗ $ .succ .zero
def D' := Nat.succ .zero

def E  := proj₂ $ .injᵣ $ true
def E' := true

-- recursive inductive type
inductive MyNat
  | nope
  | next : MyNat → MyNat
  deriving Repr

def three : MyNat := .next $ .next $ .next .nope
def six : MyNat := .next $ .next $ .next $ .next $ .next $ .next .nope

def add (x y : MyNat) : MyNat := match x with
  | .nope => y
  | .next x' => .next $ add x' y

def F  := add three three
def F' := six
