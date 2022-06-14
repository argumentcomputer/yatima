import Lean 

-- inductive TreeNode (α : Type _) where 
--   | leaf : TreeNode α 
--   | node : α → TreeNode α → TreeNode α → TreeNode α

-- mutual 

--   inductive Tree (α : Type _) where 
--   | node : α → TreeList α → Tree α

--   inductive TreeList (α : Type _) where
--   | nil : TreeList α
--   | cons : Tree α → TreeList α → TreeList α

-- end

-- mutual 

--   def size (ta : Tree α) : Nat :=
--     match ta with 
--     | Tree.node x ts => 1 + size' ts

--   def size' (ts : TreeList α) : Nat := 
--     match ts with 
--     | TreeList.nil => 0
--     | TreeList.cons t ts' => size t + size' ts'

-- end

-- #print size._mutual

inductive Tree (α : Type) where 
  | empty : Tree α
  | node : α → List (Tree α) → Tree α

namespace Tree
open Lean

def isEmpty (ta : Tree α) : Bool :=
  match ta with 
  | .empty => true
  | _ => false

instance : Inhabited (Tree α) :=
  { default := .empty }

partial def size (ta : Tree α) : Nat :=
  match ta with
  | .empty => 0
  | .node a ts => 1 + List.foldl (· + ·) 0 (ts.map size)

@[inline] protected def pure (a : α) : Tree α :=
  .node a []

@[inline] partial def bind : Tree α → (α → Tree β) → Tree β :=
  fun x b => match x with 
  | .empty => .empty 
  | (.node x ts) => 
    match b x with 
    | .empty => .empty
    | .node x' ts' => .node x' (ts' ++ List.map (fun ta => bind ta b) ts)

instance : Monad Tree where
  pure := Tree.pure
  bind := Tree.bind

mutual 

  partial def preorder (ta : Tree α) : List α :=
    match ta with 
    | .empty => []
    | .node x ts => x :: preorderF ts 
  
  partial def preorderF (ts : List $ Tree α) : List α :=
    (ts.map preorder).join

end


end Tree