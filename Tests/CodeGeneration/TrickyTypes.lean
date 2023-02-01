import TestsUtils.CodeGenAndRunTests

open LSpec in
def main := do
  let tSeq ← extractCodeGenTests
    ("Fixtures" / "CodeGeneration" / "TrickyTypes.lean")
    [ ("exprCtor", "lam"),
      ("univCtor", "zero"),
      ("nameStr", "this.is.a.name")]
  lspecIO tSeq
