import TestsUtils.CodeGenAndRunTests

open LSpec in
def main := do
  lspecIO $ ← extractCodeGenTests
    ("Fixtures" / "CodeGeneration" / "TrickyTypes.lean")
    [ ("exprCtor", "lam"),
      ("mapFind!", 1),
      ("nameStr", "this.is.a.name")]
