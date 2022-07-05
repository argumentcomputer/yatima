import Std

namespace Std.RBMap 

instance {cmp : α → α → Ordering} : Inhabited (RBMap α β cmp) where
  default := .empty

def single {cmp : α → α → Ordering} (a : α) (b : β) : RBMap α β cmp := 
  RBMap.empty.insert a b

def enumList {cmp : α → α → Ordering} (xs : List α) : RBMap α Nat cmp := 
  RBMap.ofList $ xs.enum.map (fun (x, y) => (y, x))

end Std.RBMap 

namespace YatimaStdLib

inductive Tree (α : Type) where 
  | empty : Tree α
  | node : α → List (Tree α) → Tree α
  deriving BEq, Repr

namespace Tree

def isEmpty (ta : Tree α) : Bool :=
  match ta with
  | .empty => true
  | _ => false

instance : Inhabited (Tree α) :=
  { default := .empty }

partial def toString [ToString α] (ta : Tree α) : String := 
  match ta with
  | .empty => "[]"
  | .node x ts => s!"[ node := {x} \n" ++ "\n".intercalate (ts.map toString) ++ "]"

instance [ToString α] : ToString (Tree α) :=
  { toString := toString }

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
  pure := .pure
  bind := .bind

mutual

  partial def preorder (ta : Tree α) : List α :=
    match ta with
    | .empty => []
    | .node x ts => x :: preorderF ts
  
  partial def preorderF (ts : List $ Tree α) : List α :=
    (ts.map preorder).join

end

mutual

  partial def postorder (ta : Tree α) : List α :=
    match ta with
    | .empty => []
    | .node x ts => postorderF ts ++ [x]
  
  partial def postorderF (ts : List $ Tree α) : List α :=
    (ts.map postorder).join

end

end Tree

end YatimaStdLib