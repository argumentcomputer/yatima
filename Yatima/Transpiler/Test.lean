import Lean

def array := #[1, 2, 3, 4, 5, 6]
def arrayGet1 := array.get ⟨0, by simp⟩
def arrayGet2 := array[0]
def arrayGet!1 := array.get! 0
def arrayGet!2 := array[1]!

open Lean.Compiler

set_option trace.Compiler.result true
#eval compile #[``arrayGet!2]