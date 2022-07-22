import Yatima.Store
import Yatima.ForLurkRepo.AST

namespace Yatima.Transpiler

open Yatima (Store)

abbrev State := Array (String × Lurk.Expr)

abbrev TranspileM := ReaderT Store $ EStateM String State

/-- Slow concatenation of new bindings -/
def prependBinding (b : String × Lurk.Expr) : TranspileM Unit := do
  set $ #[b].append (← get)

/-- Fast concatenation of new bindings -/
def appendBinding (b : String × Lurk.Expr) : TranspileM Unit := do
  set $ (← get).push b

def TranspileM.run (store : Store) (ste : State) (m : TranspileM α) :
    Except String State :=
  match EStateM.run (ReaderT.run m store) ste with
  | .ok _ ste  => .ok ste
  | .error e _ => .error e

/--
Takes an array of bindings in reverse order outputs a `Lurk.letE`.

Suppose that we have A and B such that B depends on A. `bindings` will be
`#[(B, β), (A, α)]` where `β` and `α` are the expressions of `B` and `A`
respectively.

The reverse order was chosen for optimization reasons, since we expect to
recursively backtrack on dependencies often and appending on arrays is faster
than prepending.
-/
def State.compile (bindings : State) : Lurk.Expr := .letE bindings.reverse.toList .currEnv

end Yatima.Transpiler
