import Yatima.Transpiler.TranspileM
import Yatima.ForLurkRepo.DSL

/-!
# Simp
A rudimentary simplifier for lurk expressions. 

* Current we only plan to support things like 
  `(|OfNat.ofNat| |Nat| n (|instOfNatNat| n)) => n`
* There is a more principled way to do this, 
  so this file should be taken as a hack and not 
  built upon heavily.
-/
open Lurk

namespace Yatima.Transpiler
namespace Simp

def getOfNatLit (e : Lurk.Expr) : Option (Fin N) := 
  match e with 
  | .app (.app (.app f nat?) n) (.app inst m) => 
    if f == ⟦$(``OfNat.ofNat)⟧ && nat? == ⟦$(``Nat)⟧ && n == m && inst == ⟦$(``instOfNatNat)⟧ then 
      match n with 
      | .lit (.num n) => some n
      | _ => none
    else 
      none
  | _ => none

end Simp
end Yatima.Transpiler