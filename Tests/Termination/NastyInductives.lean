import TestsUtils.ContAddrAndExtractTests

open LSpec in
def main := do
  lspecIO $ ← ensembleTestExtractors
    ("Fixtures" / "Termination" / "NastyInductives.lean")
    [extractTypecheckingTests]
    []
    false
