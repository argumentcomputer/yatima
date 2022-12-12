import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides2

def mixHash : Override := Override.decl ⟨``mixHash, ⟦
  (lambda (x y) (num (commit ,(x . y)))) -- TODO this is hackish, but if it works hey it works
⟧⟩

def Decidable.decide : Override := Override.decl ⟨``Decidable.decide, ⟦
  (lambda (p h) h)
⟧⟩

def decEq : Override := Override.decl ⟨``decEq, ⟦
  (lambda (α _inst a b) (_inst a b))
⟧⟩

def inferInstanceAs : Override := Override.decl ⟨``inferInstanceAs, ⟦
  (lambda (α i) i)
⟧⟩

def instDecidableNot : Override := Override.decl ⟨``instDecidableNot, ⟦
  (lambda (p dp) (not dp))
⟧⟩

def instBEq : Override := Override.decl ⟨``instBEq, ⟦
  (lambda (α inst) inst)
⟧⟩

def Miscellaneous.module := [
  mixHash,
  Decidable.decide,
  decEq,
  inferInstanceAs,
  instDecidableNot,
  instBEq
]

end Overrides2

#print Lean.HashMapImp

end Lurk