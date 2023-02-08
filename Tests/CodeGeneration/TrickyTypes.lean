import TestsUtils.CodeGenAndRunTests

open LSpec in
def main := do
  let tSeq ← extractCodeGenTests
    ("Fixtures" / "CodeGeneration" / "TrickyTypes.lean")
    [ ("exprCtor", "lam"),
      ("mapFind!", 1),
      ("nameStr", "this.is.a.name")]
  lspecIO tSeq
