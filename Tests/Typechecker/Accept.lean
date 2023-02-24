import TestsUtils.ContAddrAndExtractTests

def tcFixturesPath : System.FilePath :=
  "Fixtures" / "Typechecker"

open LSpec in
def main := do
  lspecIO $ ← ensembleTestExtractors'
    [ tcFixturesPath / "AcceptMutual.lean",
      tcFixturesPath / "AcceptFunApp.lean" ]
    [extractTypecheckingTests]
    []
