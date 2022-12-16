import TestsUtils.CompileAndExtractTests

open Lurk.Backend.DSL

open LSpec in
def main := do
  let tSeq ← extractTranspilationTests
    "Fixtures/Transpilation/TrickyTypes.lean"
    [ ("exprCtor", "lam"),
      ("univCtor", "zero"),
      ("treeSize", 2)
      -- ("nameStr",  "this.is.a.name") -- needs `commit` on `Lurk.lean`
    ]
  lspecIO tSeq
