import Yatima.Store
import Yatima.ForLurkRepo.AST

namespace Yatima.Transpiler

open Yatima (Store)

structure State where
  appends  : Array (String × Lurk.Expr)
  prepends : Array (String × Lurk.Expr)
  deriving Inhabited

abbrev TranspileM := ReaderT Store $ EStateM String State

def prependBinding (b : String × Lurk.Expr) : TranspileM Unit := do
  let s ← get
  set { s with prepends := s.prepends.push b }

def appendBinding (b : String × Lurk.Expr) : TranspileM Unit := do
  let s ← get
  set { s with appends := s.appends.push b }

def State.getBindings (s : State) : List (String × Lurk.Expr) :=
  s.prepends.reverse.append s.appends |>.data

def TranspileM.run (store : Store) (ste : State) (m : TranspileM α) :
    Except String State :=
  match EStateM.run (ReaderT.run m store) ste with
  | .ok _ ste  => .ok ste
  | .error e _ => .error e

end Yatima.Transpiler
