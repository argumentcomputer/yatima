import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides

/-! # UInt8 -/

def UInt8.toNat : Override := .decl ⟨``UInt8.toNat, ⟦
  (lambda (u) (num u))
⟧⟩

def UInt8.ofNatCore : Override := .decl ⟨``UInt8.ofNatCore, ⟦
  (lambda (n isLt) n)
⟧⟩

def UInt8.ofNat : Override := .decl ⟨``UInt8.ofNat, ⟦
  (lambda (n) (Fin.ofNat $(UInt8.size - 1) n))
⟧⟩

def UInt8.decLe : Override := .decl ⟨``UInt8.decLe, ⟦
  (lambda (a b) (to_bool (<= a b)))
⟧⟩

def UInt8.decLt : Override := .decl ⟨``UInt8.decLt, ⟦
  (lambda (a b) (to_bool (< a b)))
⟧⟩

def UInt8.decEq : Override := .decl ⟨``UInt8.decEq, ⟦
  (lambda (a b) (to_bool (= a b)))
⟧⟩

set_option pp.all true
#print Fin.shiftLeft

def UInt8.add : Override := .decl ⟨``UInt8.add, ⟦
  (lambda (a b) (Fin.add $UInt8.size $UInt8.size a b))
⟧⟩

def UInt8.sub : Override := .decl ⟨``UInt8.sub, ⟦
  (lambda (a b) (Fin.sub $UInt8.size a b))
⟧⟩

def UInt8.mul : Override := .decl ⟨``UInt8.mul, ⟦
  (lambda (a b) (Fin.mul $UInt8.size a b))
⟧⟩

def UInt8.div : Override := .decl ⟨``UInt8.div, ⟦
  (lambda (a b) (Fin.div $UInt8.size a b))
⟧⟩

def UInt8.mod : Override := .decl ⟨``UInt8.mod, ⟦
  (lambda (a b) (Fin.mod $UInt8.size a b))
⟧⟩

def UInt8.modn : Override := .decl ⟨``UInt8.modn, ⟦
  (lambda (a n) (Fin.modn $UInt8.size a b))
⟧⟩

def UInt8.land : Override := .decl ⟨``UInt8.land, ⟦
  (lambda (a b) (Fin.land $UInt8.size a b))
⟧⟩

def UInt8.lor : Override := .decl ⟨``UInt8.lor, ⟦
  (lambda (a b) (Fin.lor $UInt8.size a b))
⟧⟩

def UInt8.xor : Override := .decl ⟨``UInt8.xor, ⟦
  (lambda (a b) (Fin.xor $UInt8.size a b))
⟧⟩

-- TODO finish all these

def UInt8.shiftLeft : Override := .decl ⟨``UInt8.shiftLeft, ⟦
  (lambda (a b) (Fin.add a b))
⟧⟩

def UInt8.shiftRight : Override := .decl ⟨``UInt8.shiftRight, ⟦
  (lambda (a b) (Fin.add a b))
⟧⟩

/-! # UInt16 -/

/-! # UInt32 -/

def UInt32.toNat : Override := .decl ⟨``UInt32.toNat, ⟦
  (lambda (u) (num u))
⟧⟩

def UInt32.ofNatCore : Override := .decl ⟨``UInt32.ofNatCore, ⟦
  (lambda (n isLt) n)
⟧⟩

def UInt32.ofNat : Override := .decl ⟨``UInt32.ofNat, ⟦
  (lambda (n) (Fin.ofNat $(UInt32.size - 1) n))
⟧⟩

def UInt32.decLe : Override := .decl ⟨``UInt32.decLe, ⟦
  (lambda (a b) (to_bool (<= a b)))
⟧⟩

def UInt32.decLt : Override := .decl ⟨``UInt32.decLt, ⟦
  (lambda (a b) (to_bool (< a b)))
⟧⟩

def UInt32.decEq : Override := .decl ⟨``UInt32.decEq, ⟦
  (lambda (a b) (to_bool (= a b)))
⟧⟩

/-! # UInt64 -/

def UInt64.ofNatCore : Override := .decl ⟨``UInt64.ofNatCore, ⟦
  (lambda (n isLt) n)
⟧⟩

/-! # USize -/

def USize.toNat : Override := .decl ⟨``USize.toNat, ⟦
  (lambda (u) (num u))
⟧⟩

def USize.ofNatCore : Override := .decl ⟨``USize.ofNatCore, ⟦
  (lambda (n isLt) n)
⟧⟩

private def USize.size : AST := AST.num $ _root_.USize.size - 1

def USize.ofNat : Override := .decl ⟨``USize.ofNat, ⟦
  (lambda (n) (Fin.ofNat $USize.size n))
⟧⟩

def USize.decLe : Override := .decl ⟨``USize.decLe, ⟦
  (lambda (a b) (to_bool (<= a b)))
⟧⟩

def USize.decLt : Override := .decl ⟨``USize.decLt, ⟦
  (lambda (a b) (to_bool (< a b)))
⟧⟩

def USize.decEq : Override := .decl ⟨``USize.decEq, ⟦
  (lambda (a b) (to_bool (= a b)))
⟧⟩

def UInt.module : List Override := [
  UInt32.toNat,
  UInt32.ofNatCore,
  UInt32.ofNat,
  UInt32.decLe,
  UInt32.decLt,
  UInt32.decEq,
  UInt64.ofNatCore
]

end Overrides

end Lurk