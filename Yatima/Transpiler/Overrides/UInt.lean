import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides2

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

def UInt32.decEq : Override := .decl ⟨``UInt32.decEq, ⟦
  (lambda (a b) (to_bool (= a b)))
⟧⟩

def UInt64.ofNatCore : Override := .decl ⟨``UInt64.ofNatCore, ⟦
  (lambda (n isLt) n)
⟧⟩

def UInt.module : List Override := [
  UInt32.toNat,
  UInt32.ofNatCore,
  UInt32.ofNat,
  UInt32.decLe,
  UInt32.decEq,
  UInt64.ofNatCore
]

end Overrides2

end Lurk