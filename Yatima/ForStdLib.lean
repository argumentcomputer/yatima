import Std

namespace YatimaStdLib

abbrev RBSet (α : Type u) [ord : Ord α] := Std.RBMap α Unit ord.compare

namespace RBSet

variable [Ord α]

open Std (RBMap)

def empty : RBSet α :=
  .empty

def insert : RBSet α → α → RBSet α
  | s, a => RBMap.insert s a ()

def contains : RBSet α → α → Bool
  | s, a => RBMap.contains s a

def fold (t : RBSet α) (f : σ → α → σ) (init : σ) : σ :=
  RBMap.fold (fun acc a _ => f acc a) init t

def union (rbₗ rbᵣ : RBSet α) : RBSet α :=
  if rbₗ.size < rbᵣ.size then
    rbₗ.fold (init := rbᵣ) fun acc a => acc.insert a
  else
    rbᵣ.fold (init := rbₗ) fun acc a => acc.insert a

notation l " ⋃ₛ " r => RBSet.union l r

end RBSet

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

namespace Std.RBMap

def findM {ordering : α → α → Ordering} [Monad m] [MonadExcept ε m] 
  (rbmap : Std.RBMap α β ordering) (a : α) (e : ε) : m β :=
  match rbmap.find? a with 
  | some b => pure b
  | none => throw e

instance [ToString α] [ToString β] {ordering : α → α → Ordering} : 
  ToString (Std.RBMap α β ordering) :=
  { toString := fun rbmap => s!"{rbmap.toList}" }

end Std.RBMap

namespace List

def eraseDup [BEq α] : List α → List α
  | [] => []
  | x::xs => 
    let exs := eraseDup xs
    if exs.contains x then exs else x::exs

def splitAtP [BEq α] (p : α → Bool) (l : List α) : List α × List α :=
  match l.dropWhile p with 
  | [] => unreachable!
  | a::as => ⟨l.takeWhile p ++ [a], as⟩

partial def mergeM [Monad μ] (cmp: α → α → μ Ordering) : List α → List α → μ (List α)
  | as@(a::as'), bs@(b::bs') => do
    if (← cmp a b) == Ordering.gt
    then List.cons b <$> mergeM cmp as bs'
    else List.cons a <$> mergeM cmp as' bs
  | [], bs => return bs
  | as, [] => return as

def mergePairsM [Monad μ] (cmp: α → α → μ Ordering) : List (List α) → μ (List (List α))
  | a::b::xs => List.cons <$> (mergeM cmp a b) <*> mergePairsM cmp xs
  | xs => return xs

partial def mergeAllM [Monad μ] (cmp: α → α → μ Ordering) : List (List α) → μ (List α)
  | [x] => return x
  | xs => mergePairsM cmp xs >>= mergeAllM cmp

mutual 
  partial def sequencesM [Monad μ] (cmp : α → α → μ Ordering) : List α → μ (List (List α))
    | a::b::xs => do
      if (← cmp a b) == .gt
      then descendingM cmp b [a] xs 
      else ascendingM cmp b (fun ys => a :: ys) xs
    | xs => return [xs]

  partial def descendingM [Monad μ] (cmp : α → α → μ Ordering) (a : α) (as : List α) : List α → μ (List (List α))
    | b::bs => do
      if (← cmp a b) == .gt
      then descendingM cmp b (a::as) bs
      else List.cons (a::as) <$> sequencesM cmp (b::bs)
    | [] => List.cons (a::as) <$> sequencesM cmp []

  partial def ascendingM [Monad μ] (cmp : α → α → μ Ordering) (a : α) (as : List α → List α) : List α → μ (List (List α))
    | b::bs => do
      if (← cmp a b) != .gt
      then ascendingM cmp b (fun ys => as (a :: ys)) bs
      else List.cons (as [a]) <$> sequencesM cmp (b::bs)
    | [] => List.cons (as [a]) <$> sequencesM cmp []

end

def sortByM [Monad μ] (xs: List α) (cmp: α -> α -> μ Ordering) : μ (List α) :=
  sequencesM cmp xs >>= mergeAllM cmp

def sortBy (cmp : α -> α -> Ordering) (xs: List α) : List α := 
  Id.run do xs.sortByM (cmp <$> · <*> ·)

def sort [Ord α] (xs: List α) : List α := 
  sortBy compare xs

def groupByMAux [Monad μ] (eq : α → α → μ Bool) : List α → List (List α) → μ (List (List α))
  | a::as, (ag::g)::gs => do match (← eq a ag) with
    | true  => groupByMAux eq as ((a::ag::g)::gs)
    | false => groupByMAux eq as ([a]::(ag::g).reverse::gs)
  | _, gs => return gs.reverse

def groupByM [Monad μ] (p : α → α → μ Bool) : List α → μ (List (List α))
  | []    => return []
  | a::as => groupByMAux p as [[a]]

def joinM [Monad μ] : List (List α) → μ (List α)
  | []      => return []
  | a :: as => do return a ++ (← joinM as)

end List
