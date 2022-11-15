import Lurk.Syntax.DSL
import Lurk.Field

/-!
# Simp
A rudimentary simplifier for lurk expressions. 
* Current we only plan to support things like 
  `(|OfNat.ofNat| |Nat| n (|instOfNatNat| n)) => n`
* There is a more principled way to do this, 
  so this file should be taken as a hack and not 
  built upon heavily.
-/
namespace Yatima.Transpiler.Simp

open Lurk.Syntax AST DSL in
def getOfNatLit : AST → Option Nat
  | ~[~[~[f, nat?], n], ~[inst, m]] =>
    if f == ⟦$(``OfNat.ofNat)⟧ && nat? == ⟦$(``Nat)⟧ && n == m &&
        inst == ⟦$(``instOfNatNat)⟧ then
      match n with
      | .num n => some n
      | _ => none
    else
      none
  | _ => none

end Yatima.Transpiler.Simp
