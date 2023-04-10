import TestsUtils.CodeGenAndRunTests

open LSpec in
def main := do
  lspecIO $ ← extractCodeGenTests
    ("Fixtures" / "CodeGeneration" / "LNock.lean")
    [ ("res", "41")]