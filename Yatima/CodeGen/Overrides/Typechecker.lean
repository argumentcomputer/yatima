import Yatima.CodeGen.Override

namespace Lurk.Overrides

open Lurk Expr.DSL LDON.DSL DSL
open Yatima.CodeGen

namespace Yatima.Typechecker

def derefConst : Override := Override.decl ⟨`Yatima.Typechecker.derefConst, ⟦
  (lambda (f store) (open f))
⟧⟩

def mkInductiveProjF : Override := Override.decl ⟨`Yatima.Typechecker.mkInductiveProjF, ⟦
  (lambda (block idx quick)
    (num (commit
      (Yatima.IR.Const.inductiveProj
        (Yatima.IR.InductiveProj.mk block idx)))))
⟧⟩

def mkConstructorProjF : Override := Override.decl ⟨`Yatima.Typechecker.mkConstructorProjF, ⟦
  (lambda (block idx cidx quick)
    (num (commit
      (Yatima.IR.Const.constructorProj
        (Yatima.IR.ConstructorProj.mk block idx cidx)))))
⟧⟩

def mkRecursorProjF : Override := Override.decl ⟨`Yatima.Typechecker.mkRecursorProjF, ⟦
  (lambda (block idx ridx quick)
    (num (commit
      (Yatima.IR.Const.recursorProj
        (Yatima.IR.RecursorProj.mk block idx ridx)))))
⟧⟩

def mkDefinitionProjF : Override := Override.decl ⟨`Yatima.Typechecker.mkDefinitionProjF, ⟦
  (lambda (block idx quick)
    (num (commit
      (Yatima.IR.Const.definitionProj
        (Yatima.IR.DefinitionProj.mk block idx)))))
⟧⟩

def module := [
  derefConst,
  mkInductiveProjF,
  mkConstructorProjF,
  mkRecursorProjF,
  mkDefinitionProjF
]

end Yatima.Typechecker

end Lurk.Overrides
