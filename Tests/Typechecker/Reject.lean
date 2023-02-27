import TestsUtils.ContAddrAndExtractTests

def tcFixturesPath : System.FilePath :=
  "Fixtures" / "Typechecker"

open LSpec in
def main := do
  lspecIO $ ← ensembleTestExtractors'
    [ --tcFixturesPath / "RejectInfListFalse.lean",
      tcFixturesPath / "RejectMetaFalse.lean",
      tcFixturesPath / "RejectAxiomFalse.lean",
      tcFixturesPath / "RejectSorry.lean" ]
    [extractNonTypecheckingTests]
    []
