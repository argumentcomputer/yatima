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

def three : MyNat := .next $ .next $ .next .nope

def add' (x y : MyNat) : MyNat := match x with
  | .nope    => y
  | .next x' => .next $ add' x' y

-- force definition via primitive recursor
@[implementedBy add'] def add (x y : MyNat) : MyNat := by
  induction x with
  | nope => exact y
  | next _ sum => exact .next sum

#print add

def F  : MyNat := add three three
def F' : MyNat := .next $ .next $ .next $ .next $ .next $ .next .nope

def G  : MyNat := add' three three
def G' : MyNat := .next $ .next $ .next $ .next $ .next $ .next .nope
