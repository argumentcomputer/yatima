import Lean
import Yatima.Compiler.CompileM

namespace Yatima.Compiler
/- mergesort implementation based on https://hackage.haskell.org/package/base-4.16.1.0/docs/src/Data-OldList.html#sort -/

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
    else List.cons (a::as) <$> sequencesM cmp bs
  | [] => List.cons (a::as) <$> sequencesM cmp []

  partial def ascendingM [Monad μ] (cmp : α → α → μ Ordering) (a : α) (as : List α → List α) : List α → μ (List (List α))
  | b::bs => do
    if (← cmp a b) != .gt
    then ascendingM cmp b (fun ys => as (a :: ys)) bs
    else List.cons (as [a]) <$> sequencesM cmp bs
  | [] => List.cons (as [a]) <$> sequencesM cmp []
end

def sortByM [Monad μ] (cmp: α -> α -> μ Ordering) (xs: List α) : μ (List α) := do
  sequencesM cmp xs >>= mergeAllM cmp

--def referenceMap (constMap : Lean.ConstMap) : RBMap Lean.Name (List Lean.Name) := sorry
--
--def detectCycles (constMap : Lean.ConstMap) : List (List Lean.Name) := sorry

instance : HMul Ordering Ordering Ordering where
  hMul
  | .gt, _ => .gt
  | .lt, _ => .lt
  | .eq, x => x

end Yatima.Compiler
--def compareMutDef (names : List Lean.Name) (x: Lean.DefinitionVal) (y: Lean.DefinitionVal) : Ordering :=
--  concatOrds
--    [ compare x.levelParams.length y.levelParams.length
--    , compare x.type y.type
--    , compare x.value y.value
--    ]
--
--
--
--def sortMutDef (ds: List Lean.DefinitionVal): List Lean.DefinitionVal := 
--  let names : List Lean.Name := List.map (fun x => x.name) ds
--  sortBy (compareMutDef names) ds
--
