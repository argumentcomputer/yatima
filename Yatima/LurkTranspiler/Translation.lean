import Yatima.Store
import Yatima.ForLurkRepo.Printer

open Yatima

abbrev State := Array (String × Lurk.Expr)

abbrev TranslateM := ReaderT Store $ EStateM String State

def compileBindings (bindings : State) : Lurk.Expr := sorry

def TranslateM.run (store : Store) (ste : State) (m : TranslateM α) :
    Except String String :=
  match EStateM.run (ReaderT.run m store) ste with
  | .ok _ ste  => .ok (compileBindings ste).print
  | .error e _ => .error e

def toLurkExpr (cid : ConstCid) (const : Const) : TranslateM Lurk.Expr := sorry

/-- Main translation function -/
def translateM : TranslateM String := do
  let store ← read
  store.const_cache.forM 
    fun cid const => do 
      let newExpr ← toLurkExpr cid const
      let newExprName : String := const.name
      set $ (← get).append #[(newExprName, newExpr)]
  return (compileBindings (← get)).print

def translate (store : Store) : Except String String :=
  TranslateM.run store #[] (translateM store)
