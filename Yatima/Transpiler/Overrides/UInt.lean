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

def UInt8.add : Override := .decl ⟨``UInt8.add, ⟦
  (lambda (a b) (Fin.add $UInt8.size a b))
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
  (lambda (a n) (Fin.modn $UInt8.size a n))
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

def UInt8.shiftLeft : Override := .decl ⟨``UInt8.shiftLeft, ⟦
  (lambda (a b) (Fin.shiftLeft $UInt8.size a (Nat.mod b 8)))
⟧⟩

def UInt8.shiftRight : Override := .decl ⟨``UInt8.shiftRight, ⟦
  (lambda (a b) (Fin.shiftRight $UInt8.size a (Nat.mod b 8)))
⟧⟩

def UInt8.module : List Override := [
  UInt8.toNat,
  UInt8.ofNatCore,
  UInt8.ofNat,
  UInt8.decLe,
  UInt8.decLt,
  UInt8.decEq,
  UInt8.add,
  UInt8.sub,
  UInt8.mul,
  UInt8.div,
  UInt8.mod,
  UInt8.modn,
  UInt8.land,
  UInt8.lor,
  UInt8.xor,
  UInt8.shiftLeft,
  UInt8.shiftRight
]

/-! # UInt16 -/

def UInt16.toNat : Override := .decl ⟨``UInt16.toNat, ⟦
  (lambda (u) (num u))
⟧⟩

def UInt16.ofNatCore : Override := .decl ⟨``UInt16.ofNatCore, ⟦
  (lambda (n isLt) n)
⟧⟩

def UInt16.ofNat : Override := .decl ⟨``UInt16.ofNat, ⟦
  (lambda (n) (Fin.ofNat $(UInt16.size - 1) n))
⟧⟩

def UInt16.decLe : Override := .decl ⟨``UInt16.decLe, ⟦
  (lambda (a b) (to_bool (<= a b)))
⟧⟩

def UInt16.decLt : Override := .decl ⟨``UInt16.decLt, ⟦
  (lambda (a b) (to_bool (< a b)))
⟧⟩

def UInt16.decEq : Override := .decl ⟨``UInt16.decEq, ⟦
  (lambda (a b) (to_bool (= a b)))
⟧⟩

def UInt16.add : Override := .decl ⟨``UInt16.add, ⟦
  (lambda (a b) (Fin.add $UInt16.size a b))
⟧⟩

def UInt16.sub : Override := .decl ⟨``UInt16.sub, ⟦
  (lambda (a b) (Fin.sub $UInt16.size a b))
⟧⟩

def UInt16.mul : Override := .decl ⟨``UInt16.mul, ⟦
  (lambda (a b) (Fin.mul $UInt16.size a b))
⟧⟩

def UInt16.div : Override := .decl ⟨``UInt16.div, ⟦
  (lambda (a b) (Fin.div $UInt16.size a b))
⟧⟩

def UInt16.mod : Override := .decl ⟨``UInt16.mod, ⟦
  (lambda (a b) (Fin.mod $UInt16.size a b))
⟧⟩

def UInt16.modn : Override := .decl ⟨``UInt16.modn, ⟦
  (lambda (a n) (Fin.modn $UInt16.size a n))
⟧⟩

def UInt16.land : Override := .decl ⟨``UInt16.land, ⟦
  (lambda (a b) (Fin.land $UInt16.size a b))
⟧⟩

def UInt16.lor : Override := .decl ⟨``UInt16.lor, ⟦
  (lambda (a b) (Fin.lor $UInt16.size a b))
⟧⟩

def UInt16.xor : Override := .decl ⟨``UInt16.xor, ⟦
  (lambda (a b) (Fin.xor $UInt16.size a b))
⟧⟩

def UInt16.shiftLeft : Override := .decl ⟨``UInt16.shiftLeft, ⟦
  (lambda (a b) (Fin.shiftLeft $UInt16.size a (Nat.mod b 16)))
⟧⟩

def UInt16.shiftRight : Override := .decl ⟨``UInt16.shiftRight, ⟦
  (lambda (a b) (Fin.shiftRight $UInt16.size a (Nat.mod b 16)))
⟧⟩

def UInt16.module : List Override := [
  UInt16.toNat,
  UInt16.ofNatCore,
  UInt16.ofNat,
  UInt16.decLe,
  UInt16.decLt,
  UInt16.decEq,
  UInt16.add,
  UInt16.sub,
  UInt16.mul,
  UInt16.div,
  UInt16.mod,
  UInt16.modn,
  UInt16.land,
  UInt16.lor,
  UInt16.xor,
  UInt16.shiftLeft,
  UInt16.shiftRight
]

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

def UInt32.add : Override := .decl ⟨``UInt32.add, ⟦
  (lambda (a b) (Fin.add $UInt32.size a b))
⟧⟩

def UInt32.sub : Override := .decl ⟨``UInt32.sub, ⟦
  (lambda (a b) (Fin.sub $UInt32.size a b))
⟧⟩

def UInt32.mul : Override := .decl ⟨``UInt32.mul, ⟦
  (lambda (a b) (Fin.mul $UInt32.size a b))
⟧⟩

def UInt32.div : Override := .decl ⟨``UInt32.div, ⟦
  (lambda (a b) (Fin.div $UInt32.size a b))
⟧⟩

def UInt32.mod : Override := .decl ⟨``UInt32.mod, ⟦
  (lambda (a b) (Fin.mod $UInt32.size a b))
⟧⟩

def UInt32.modn : Override := .decl ⟨``UInt32.modn, ⟦
  (lambda (a n) (Fin.modn $UInt32.size a n))
⟧⟩

def UInt32.land : Override := .decl ⟨``UInt32.land, ⟦
  (lambda (a b) (Fin.land $UInt32.size a b))
⟧⟩

def UInt32.lor : Override := .decl ⟨``UInt32.lor, ⟦
  (lambda (a b) (Fin.lor $UInt32.size a b))
⟧⟩

def UInt32.xor : Override := .decl ⟨``UInt32.xor, ⟦
  (lambda (a b) (Fin.xor $UInt32.size a b))
⟧⟩

def UInt32.shiftLeft : Override := .decl ⟨``UInt32.shiftLeft, ⟦
  (lambda (a b) (Fin.shiftLeft $UInt32.size a (Nat.mod b 32)))
⟧⟩

def UInt32.shiftRight : Override := .decl ⟨``UInt32.shiftRight, ⟦
  (lambda (a b) (Fin.shiftRight $UInt32.size a (Nat.mod b 32)))
⟧⟩

def UInt32.module : List Override := [
  UInt32.toNat,
  UInt32.ofNatCore,
  UInt32.ofNat,
  UInt32.decLe,
  UInt32.decLt,
  UInt32.decEq,
  UInt32.add,
  UInt32.sub,
  UInt32.mul,
  UInt32.div,
  UInt32.mod,
  UInt32.modn,
  UInt32.land,
  UInt32.lor,
  UInt32.xor,
  UInt32.shiftLeft,
  UInt32.shiftRight
]



/-! # UInt64 -/

def UInt64.toNat : Override := .decl ⟨``UInt64.toNat, ⟦
  (lambda (u) (num u))
⟧⟩

def UInt64.ofNatCore : Override := .decl ⟨``UInt64.ofNatCore, ⟦
  (lambda (n isLt) n)
⟧⟩

def UInt64.ofNat : Override := .decl ⟨``UInt64.ofNat, ⟦
  (lambda (n) (Fin.ofNat $(UInt64.size - 1) n))
⟧⟩

def UInt64.decLe : Override := .decl ⟨``UInt64.decLe, ⟦
  (lambda (a b) (to_bool (<= a b)))
⟧⟩

def UInt64.decLt : Override := .decl ⟨``UInt64.decLt, ⟦
  (lambda (a b) (to_bool (< a b)))
⟧⟩

def UInt64.decEq : Override := .decl ⟨``UInt64.decEq, ⟦
  (lambda (a b) (to_bool (= a b)))
⟧⟩

def UInt64.add : Override := .decl ⟨``UInt64.add, ⟦
  (lambda (a b) (Fin.add $UInt64.size a b))
⟧⟩

def UInt64.sub : Override := .decl ⟨``UInt64.sub, ⟦
  (lambda (a b) (Fin.sub $UInt64.size a b))
⟧⟩

def UInt64.mul : Override := .decl ⟨``UInt64.mul, ⟦
  (lambda (a b) (Fin.mul $UInt64.size a b))
⟧⟩

def UInt64.div : Override := .decl ⟨``UInt64.div, ⟦
  (lambda (a b) (Fin.div $UInt64.size a b))
⟧⟩

def UInt64.mod : Override := .decl ⟨``UInt64.mod, ⟦
  (lambda (a b) (Fin.mod $UInt64.size a b))
⟧⟩

def UInt64.modn : Override := .decl ⟨``UInt64.modn, ⟦
  (lambda (a n) (Fin.modn $UInt64.size a n))
⟧⟩

def UInt64.land : Override := .decl ⟨``UInt64.land, ⟦
  (lambda (a b) (Fin.land $UInt64.size a b))
⟧⟩

def UInt64.lor : Override := .decl ⟨``UInt64.lor, ⟦
  (lambda (a b) (Fin.lor $UInt64.size a b))
⟧⟩

def UInt64.xor : Override := .decl ⟨``UInt64.xor, ⟦
  (lambda (a b) (Fin.xor $UInt64.size a b))
⟧⟩

def UInt64.shiftLeft : Override := .decl ⟨``UInt64.shiftLeft, ⟦
  (lambda (a b) (Fin.shiftLeft $UInt64.size a (Nat.mod b 64)))
⟧⟩

def UInt64.shiftRight : Override := .decl ⟨``UInt64.shiftRight, ⟦
  (lambda (a b) (Fin.shiftRight $UInt64.size a (Nat.mod b 64)))
⟧⟩

def UInt64.module : List Override := [
  UInt64.toNat,
  UInt64.ofNatCore,
  UInt64.ofNat,
  UInt64.decLe,
  UInt64.decLt,
  UInt64.decEq,
  UInt64.add,
  UInt64.sub,
  UInt64.mul,
  UInt64.div,
  UInt64.mod,
  UInt64.modn,
  UInt64.land,
  UInt64.lor,
  UInt64.xor,
  UInt64.shiftLeft,
  UInt64.shiftRight
]

/-! # USize -/

/-- If we don't do this, we get the error  -/
-- private def USize.size : AST := AST.num $ _root_.USize.size

def USize.toNat : Override := .decl ⟨``USize.toNat, ⟦
  (lambda (u) (num u))
⟧⟩

def USize.ofNatCore : Override := .decl ⟨``USize.ofNatCore, ⟦
  (lambda (n isLt) n)
⟧⟩

/-- If we do `$(USize.size - 1)`, we get the error 
```
failed to compile definition, consider marking it as 'noncomputable' 
because it depends on 'Nat.pow.match_1', and it does not have executable code
```
-/
def USize.ofNat : Override := .decl ⟨``USize.ofNat, ⟦
  (lambda (n) (Fin.ofNat (- 1 $USize.size) n))
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

def USize.add : Override := .decl ⟨``USize.add, ⟦
  (lambda (a b) (Fin.add $USize.size a b))
⟧⟩

def USize.sub : Override := .decl ⟨``USize.sub, ⟦
  (lambda (a b) (Fin.sub $USize.size a b))
⟧⟩

def USize.mul : Override := .decl ⟨``USize.mul, ⟦
  (lambda (a b) (Fin.mul $USize.size a b))
⟧⟩

def USize.div : Override := .decl ⟨``USize.div, ⟦
  (lambda (a b) (Fin.div $USize.size a b))
⟧⟩

def USize.mod : Override := .decl ⟨``USize.mod, ⟦
  (lambda (a b) (Fin.mod $USize.size a b))
⟧⟩

def USize.modn : Override := .decl ⟨``USize.modn, ⟦
  (lambda (a n) (Fin.modn $USize.size a n))
⟧⟩

def USize.land : Override := .decl ⟨``USize.land, ⟦
  (lambda (a b) (Fin.land $USize.size a b))
⟧⟩

def USize.lor : Override := .decl ⟨``USize.lor, ⟦
  (lambda (a b) (Fin.lor $USize.size a b))
⟧⟩

def USize.xor : Override := .decl ⟨``USize.xor, ⟦
  (lambda (a b) (Fin.xor $USize.size a b))
⟧⟩

def USize.shiftLeft : Override := .decl ⟨``USize.shiftLeft, ⟦
  (lambda (a b) (Fin.shiftLeft $USize.size a (Nat.mod b 32)))
⟧⟩

def USize.shiftRight : Override := .decl ⟨``USize.shiftRight, ⟦
  (lambda (a b) (Fin.shiftRight $USize.size a (Nat.mod b 32)))
⟧⟩

def USize.module : List Override := [
  USize.toNat,
  USize.ofNatCore,
  USize.ofNat,
  USize.decLe,
  USize.decLt,
  USize.decEq,
  USize.add,
  USize.sub,
  USize.mul,
  USize.div,
  USize.mod,
  USize.modn,
  USize.land,
  USize.lor,
  USize.xor,
  USize.shiftLeft,
  USize.shiftRight
]

def UInt.module : List Override := 
  UInt8.module ++
  UInt16.module ++
  UInt32.module ++
  UInt64.module ++
  USize.module

end Overrides

end Lurk