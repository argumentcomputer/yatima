import Lurk.Syntax.AST

/-!
# Simp
A rudimentary simplifier for lurk expressions. 
* Current we only plan to support things like 
  `(((OfNat.ofNat Nat) n) (instOfNatNat n)) => n`
* There is a more principled way to do this, 
  so this file should be taken as a hack and not 
  built upon heavily.
-/
namespace Yatima.Transpiler.Simp

open Lurk.Syntax AST in
def getOfNatLit : AST → AST
  | x@~[
      ~[~[sym "OfNat.ofNat", sym "Nat"], num n], -- ((OfNat.ofNat Nat) n)
      ~[sym "instOfNatNat", num m]               -- (instOfNatNat n)
    ] => if n == m then num n else x
  | x => x

end Yatima.Transpiler.Simp
