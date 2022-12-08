import Lurk.Syntax.DSL
import Yatima.Transpiler2.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler2

namespace Overrides2

def UInt32ToNat : Override := .decl ⟨``UInt32.toNat, ⟦
  (lambda (u) (num u))
⟧⟩

def UInt64.ofNatCore : Override := .decl ⟨``UInt64.ofNatCore, ⟦
  (lambda (n isLt) n)
⟧⟩

end Overrides2

end Lurk