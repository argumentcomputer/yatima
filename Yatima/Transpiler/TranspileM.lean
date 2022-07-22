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

end Yatima.Transpiler
