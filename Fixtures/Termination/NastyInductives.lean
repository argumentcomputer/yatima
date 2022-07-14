prelude

inductive Option (α : Type u) where 
  | none : Option α
  | some (a : α) : Option α

inductive List (α : Type u) where 
  | nil : List α
  | cons (a : α) (as : List α) : List α

-- nested inductive
inductive Treew (A : Type) where
  | branch : (a : A) → (trees : List (Treew A)) → Treew A

-- multiply nested inductive
inductive Treer (A : Type) where
  | branch : (a : A) → (tree? : Option (Treer A)) → (trees : List (Treer A)) → Treer A

mutual

  -- mutual and multiply nested inductive
  inductive Treeq (A : Type) where
    | branch : TreeListq A → (a : A) → (tree? : Option (Treer A)) → (trees : List (Treeq A)) → Treeq A

  inductive TreeListq (A : Type) where
    | nil : TreeListq A
    | cons : (t : Treeq A) → (ts : TreeListq A) → TreeListq A

  inductive TreeListx (A : Type) where
    | nil : TreeListx A
    | cons : (t : Treeq A) → (ts : TreeListx A) → TreeListx A

end
