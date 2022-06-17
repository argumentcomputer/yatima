import Yatima.Compiler.CompileM
import Yatima.Graph.Graph

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

def sortByM [Monad μ] (cmp: α -> α -> μ Ordering) (xs: List α) : μ (List α) :=
  sequencesM cmp xs >>= mergeAllM cmp

instance : HMul Ordering Ordering Ordering where
  hMul
  | .gt, _ => .gt
  | .lt, _ => .lt
  | .eq, x => x

def printInfo : CompileM Unit := do 
  dbg_trace "\n\nInfo:"
  dbg_trace s!"`univ_cache` size: {(← get).env.univ_cache.size}"
  dbg_trace s!"`expr_cache` size: {(← get).env.expr_cache.size}"
  dbg_trace s!"`const_cache` size: {(← get).env.const_cache.size}"
  dbg_trace s!"`constMap` size: {(← read).constMap.size}"
  dbg_trace s!"`cache` size: {(← get).cache.size}"
  dbg_trace s!"`cache`: {(← get).cache.toList.map Prod.fst}"
  -- dbg_trace s!"`WWW._mutual`: {((← get).cache.toList.map Prod.fst).contains }"

end Yatima.Compiler
