import TestsUtils.ContAddrAndExtractTests

open Lurk.Backend.DSL

open LSpec in
def main := do
  let tSeq ← extractTranspilationTests
    "Fixtures/Transpilation/TrickyTypes.lean"
    [ ("exprCtor", "lam"), -- TODO: needs `commit` on `Lurk.lean`
      ("univCtor", "zero"), 
      ("treeSize", 2),
      ("nameStr",  "this.is.a.name") -- TODO: needs `commit` on `Lurk.lean`
    ]
  lspecIO tSeq
