import LSpec
import Lurk.Backend.Eval
import Yatima.CodeGen.CodeGen
import Yatima.Lean.Utils

open LSpec Yatima

open CodeGen Lurk Backend

instance [BEq α] [BEq β] : BEq (Except α β) where beq
  | .ok x, .ok y => x == y
  | .error x, .error y => x == y
  | _, _ => false

def extractCodeGenTests (fixture : String) (expect : List (String × Value)) : IO TestSeq := do
  Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend ⟨fixture⟩
  expect.foldlM (init := .done) fun tSeq (root, expected) => do
    return withExceptOk s!"Code generation of {root} succeeds" (codeGen leanEnv root) fun expr =>
      withExceptOk s!"Evaluation of {root} succeeds" expr.eval fun val =>
        tSeq ++ test s!"Evaluation of {root}, resulting in {val}, yields {expected}"
          (val == expected)
