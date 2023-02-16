prelude -- Don't import Init, because we're in Init itself
set_option linter.all false -- prevent error messages from runFrontend

universe u v w

structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β

#print Prod.fst
#print Prod.rec