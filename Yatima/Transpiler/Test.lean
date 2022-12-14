import Lean
import Yatima.Transpiler.PrettyPrint

open Lean Meta

def array := #[1, 2, 3, 4, 5, 6]
def arrayGet1 := array.get ⟨0, by simp⟩
def arrayGet2 := array[0]
def arrayGet!1 := array.get! 0
def arrayGet!2 := array[1]!

def band (n m : Nat) := 
  let x := Nat.bitwise and n m
  dbg_trace x
  x

open Lean.Compiler

set_option trace.Compiler.result true
#eval compile #[``band]

def test : MetaM Unit := do
  let some decl ← Lean.Compiler.LCNF.getMonoDecl? `Lean.AssocList.toList |
    throwError "what"
  IO.println $ Yatima.Transpiler.ppDecl decl

#eval test