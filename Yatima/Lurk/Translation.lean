import Yatima.Store
import Yatima.Lurk.AST

open Yatima

-- abbrev Context := Store

abbrev State := Array (String × Lurk.Expr)

abbrev TranslateM := ReaderT Store $ EStateM String State

def TranslateM.run (store : Store) (m : TranslateM α):= ReaderT.run m store 

def toLurkExpr (cid : ConstCid) (const : Const) : TranslateM Lurk.Expr := sorry

def compileBindings (bindings : State) : Lurk.Expr := sorry

/--
Main translation function
-/
def translateM : TranslateM Lurk.Expr := do
  let store ← read
  store.const_cache.forM 
    fun cid const => do 
      let newExpr ← toLurkExpr cid const
      let newExprName : String := const.name
      set $ (←get).append #[(newExprName, newExpr)]
  return compileBindings (← get)


#check Ipld.Const
-- def translate (store : Store) := match TranslateM.run store (translateM store) with
--   | .error msg => sorry
