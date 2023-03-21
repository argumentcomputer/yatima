import LSpec
import Lurk.Eval
import Yatima.CodeGen.CodeGen
import Yatima.Lean.Utils

open LSpec Yatima CodeGen Lurk
open System (FilePath)

def extractCodeGenTests (source : FilePath) (expect : List (String × Value)) :
    IO TestSeq := do
  Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend (← IO.FS.readFile source) source
  pure $ expect.foldl (init := .done) fun tSeq (root, expected) =>
    withExceptOk s!"Code generation of {root} succeeds" (codeGen leanEnv root) fun expr =>
      withExceptOk s!"Evaluation of {root} succeeds" expr.evaluate' fun val =>
        tSeq ++ test s!"Evaluation of {root}, resulting in {val}, yields {expected}"
          (val == expected)
