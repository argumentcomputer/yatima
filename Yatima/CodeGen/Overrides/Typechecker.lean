import Yatima.CodeGen.Override

namespace Lurk.Overrides

open Lurk.Backend DSL
open Yatima.CodeGen

namespace Yatima.Typechecker

def derefConst : Override := Override.decl ⟨`Yatima.Typechecker.derefConst, ⟦
  (lambda (f store) (open f))
⟧⟩

def mkInductiveProjF : Override := Override.decl ⟨`Yatima.Typechecker.mkInductiveProjF, ⟦
  (lambda (block idx)
    (num (commit
      (Yatima.TC.Const.inductiveProj
        (Yatima.TC.InductiveProj.mk block idx)))))
⟧⟩

def mkConstructorProjF : Override := Override.decl ⟨`Yatima.Typechecker.mkConstructorProjF, ⟦
  (lambda (block idx cidx)
    (num (commit
      (Yatima.TC.Const.constructorProj
        (Yatima.TC.ConstructorProj.mk block idx cidx)))))
⟧⟩

def mkRecursorProjF : Override := Override.decl ⟨`Yatima.Typechecker.mkRecursorProjF, ⟦
  (lambda (block idx ridx)
    (num (commit
      (Yatima.TC.Const.recursorProj
        (Yatima.TC.recursorProj.mk block idx ridx)))))
⟧⟩

def mkDefinitionProjF : Override := Override.decl ⟨`Yatima.Typechecker.mkDefinitionProjF, ⟦
  (lambda (block idx)
    (num (commit
      (Yatima.TC.Const.definitionProj
        (Yatima.TC.definitionProj.mk block idx)))))
⟧⟩

def module := [
  derefConst,
  mkConstructorProjF
]

end Yatima.Typechecker

end Lurk.Overrides
