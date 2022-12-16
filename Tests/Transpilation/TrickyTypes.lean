import TestsUtils.CompileAndExtractTests

open Lurk.Backend.DSL

open LSpec in
def main := do
  let tSeq ← extractTranspilationTests
    "Fixtures/Transpilation/TrickyTypes.lean"
    [ ("exprCtor", "lam"),
      -- ("univCtor", "zero"), -- TODO: needs `commit` on `Lurk.lean`
      ("treeSize", 2)
      -- ("nameStr",  "this.is.a.name") -- TODO: needs `commit` on `Lurk.lean`
    ]
  lspecIO tSeq
