import TestsUtils.ContAddrAndExtractTests

def defsExtractor := extractAnonGroupsTests
  [[`Nat, `MyNat, `MyOtherNat]]

open LSpec in
def main := do
  lspecIO $ ← ensembleTestExtractors
    ("Fixtures" / "AnonGroups" / "ToImport.lean")
    [defsExtractor]
    [extractGeneralTests]
