prelude
import TypeChecker.Init

namespace Monad

def seqComp {M : Type u → Type v} [Monad M] (ma : M A) (mb : M B) :=
  ma >>= fun _ => mb

def repeatM {m : Type _ → Type _} [Monad m] (f : m PUnit) : Nat → m PUnit
  | 0 => pure ()
  | n + 1 => f *> repeatM f n

partial def repeatWhile {m : Type _ → Type _} [Monad m] (test : m Bool) (f : m PUnit) : m PUnit :=
  test >>= fun b => if b then f *> (repeatWhile test f) else pure ()

end Monad
