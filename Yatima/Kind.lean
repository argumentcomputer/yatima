namespace Yatima

inductive Kind where
| Anon : Kind
| Meta : Kind
deriving BEq, Inhabited

instance : Coe Kind Bool where coe | .Anon => .true | .Meta => .false

inductive Split (A : Type) (B : Type) : (b : Bool) → Type where
| inj₁ : A → Split A B True
| inj₂ : B → Split A B False
deriving BEq

instance [Inhabited A] [Inhabited B] : Inhabited (Split A B k) where
  default := match k with | .true => .inj₁ default | .false => .inj₂ default

instance [Ord A] [Ord B] : Ord (Split A B k) where
  compare
    | .inj₁ a, .inj₁ b => compare a b
    | .inj₂ a, .inj₂ b => compare a b
    
def Split.proj₁ : Split A B True → A
  | .inj₁ a => a
    
def Split.proj₂ : Split A B False → B
  | .inj₂ b => b

instance : Coe A (Split A B .true) where coe  := .inj₁
instance : Coe B (Split A B .false) where coe := .inj₂

instance : Coe (Split A B .true) A where coe  := Split.proj₁
instance : Coe (Split A B .false) B where coe := Split.proj₂

end Yatima
