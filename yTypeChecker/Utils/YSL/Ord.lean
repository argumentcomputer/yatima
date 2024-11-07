prelude
import yTypeChecker.Init

namespace Ord

instance [Ord α] [Ord β] : Ord (α × β) where compare
  | (a₁, b₁), (a₂, b₂) => match compare a₁ a₂ with
    | .eq => compare b₁ b₂
    | x   => x

instance [Ord α] : Ord (Option α) where compare
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some a, some b => compare a b

end Ord
