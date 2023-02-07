import Yatima.CodeGen.Override

namespace Lurk.Overrides

open Lurk.Backend DSL
open Yatima.CodeGen

namespace Yatima.Typechecker

def derefConst : Override := Override.decl ⟨`Yatima.Typechecker.derefConst, ⟦
  (lambda (f store) (open f))
⟧⟩

def mkConstructorProjF : Override := Override.decl ⟨`Yatima.Typechecker.mkConstructorProjF, ⟦
  (lambda (block idx cidx) 
    (num (commit 
      (Yatima.TC.Const.constructorProj
        (Yatima.TC.ConstructorProj.mk block idx cidx)))))
⟧⟩

def module := [
  derefConst,
  mkConstructorProjF
]

end Yatima.Typechecker

end Lurk.Overrides
