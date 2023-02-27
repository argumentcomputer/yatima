import TestsUtils.ContAddrAndExtractTests

open LSpec in
def main := do
  lspecIO $ ← ensembleTestExtractors
    ("Fixtures" / "Termination" / "TrickyDef.lean")
    [extractTypecheckingTests]
    []
