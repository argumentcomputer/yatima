namespace Yatima

/-- Similar to `Prod`, but carries extra data to lock projections -/
inductive Split (A : Type) (B : Type) : Bool → Type where
  | injₗ : A → Split A B true
  | injᵣ : B → Split A B false
  deriving BEq, Repr

/-- The left projection of `Yatima.Split` -/
def Split.projₗ : Split A B true → A
  | .injₗ a => a

/-- The right projection of `Yatima.Split` -/
def Split.projᵣ : Split A B false → B
  | .injᵣ b => b

instance [Inhabited A] [Inhabited B] : Inhabited (Split A B k) where
  default := match k with
    | true  => .injₗ default
    | false => .injᵣ default

instance [Ord A] [Ord B] : Ord (Split A B k) where compare
  | .injₗ a, .injₗ b => compare a b
  | .injᵣ a, .injᵣ b => compare a b

instance : Coe A (Split A B true)  := ⟨.injₗ⟩
instance : Coe B (Split A B false) := ⟨.injᵣ⟩

end Yatima
