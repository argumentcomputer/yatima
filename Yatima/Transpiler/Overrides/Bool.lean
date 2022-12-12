import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides

def not : Override := Override.decl ⟨``not, ⟦
  (lambda (x)
    (let ((_lurk_idx (getelem x 1)))
        (if (= _lurk_idx 0)
            Bool.true
            Bool.false)))
⟧⟩

def Bool.module := [
  not
]

end Overrides

end Lurk