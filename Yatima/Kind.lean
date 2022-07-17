namespace Yatima

inductive Kind where
| Anon : Kind
| Meta : Kind
deriving BEq, Inhabited

instance : Coe Kind Bool where coe | .Anon => .true | .Meta => .false

inductive Split (A : Type) (B : Type) : (b : Bool) → Type where
| fst : A → Split A B True
| snd : B → Split A B False
deriving BEq

instance [Inhabited A] [Inhabited B] : Inhabited (Split A B k) where
  default := match k with | .true => .fst default | .false => .snd default

instance [Ord A] [Ord B] : Ord (Split A B k) where
  compare
    | .fst a, .fst b => compare a b
    | .snd a, .snd b => compare a b
    
def Split.proj₁ : Split A B True → A
  | .fst a => a
    
def Split.proj₂ : Split A B False → B
  | .snd b => b

instance : Coe A (Split A B .true) where coe  := .fst
instance : Coe B (Split A B .false) where coe := .snd

end Yatima
