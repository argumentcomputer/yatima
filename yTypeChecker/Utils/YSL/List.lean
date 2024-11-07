prelude
import yTypeChecker.Init

def compareAux [Ord α] : List α → List α → Ordering
  | [], [] => Ordering.eq
  | [], _ => Ordering.lt
  | _, [] => Ordering.gt
  | x::xs, y::ys => match compare x y with
    | Ordering.eq => compareAux xs ys
    | other => other

instance listOrd [Ord α] : Ord (List α) where
  compare := compareAux
