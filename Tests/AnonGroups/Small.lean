import TestsUtils.ContAddrAndExtractTests

def defsExtractor := extractAnonGroupsTests
  [[`PUnit]]

open LSpec in
def main := do
  lspecIO $ ← ensembleTestExtractors
    ("Fixtures" / "AnonGroups" / "Small.lean")
    [defsExtractor]
    [extractGeneralTests]
