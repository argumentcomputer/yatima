import LSpec
import Yatima.ContAddr.ContAddr
import Yatima.Commit.Commit
import Yatima.Typechecker.Typechecker

open LSpec Yatima IR ContAddr Commit Typechecker
open System (FilePath)

def withExceptOkIO (descr : String) (exc : Except ε α) [ToString ε]
    (f : α → IO TestSeq) : IO TestSeq :=
  match exc with
  | .error e => return test descr (ExpectationFailure "ok _" s!"error {e}")
  | .ok    a => return test descr true $ ← f a

abbrev Extractor := ContAddrState → TestSeq
abbrev IOExtractor := ContAddrState → IO TestSeq

def ensembleCompilationTests (source : FilePath)
  (extractors : List Extractor) (ioExtractors : List IOExtractor)
    (setPaths : Bool := true) : IO TestSeq := do
  if setPaths then Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend (← IO.FS.readFile source) source
  let (constMap, delta) := leanEnv.getConstsAndDelta
  withExceptOkIO s!"Content-addresses {source}" (contAddr constMap delta)
    fun stt => do
      let pureTests := extractors.foldl (init := .done)
        fun acc ext => acc ++ (ext stt)
      ioExtractors.foldlM (init := pureTests) fun acc ext =>
        do pure $ acc ++ (← ext stt)

def extractPersistenceTests : IOExtractor := fun stt => do
  let storeAnon := stt.storeAnon
  let storeMeta := stt.storeMeta
  stt.dump "env.yenv"
  withExceptOkIO "Loads the anon store"
      (← StoreAnon.load stt.env.anonHashes) fun storeAnon' =>
    return withExceptOk "Loads the meta store"
        (← StoreMeta.load stt.env.metaHashes) fun storeMeta' =>
      test "Anon store roundtrips" (storeAnon == storeAnon') ++
      test "Meta store roundtrips" (storeMeta == storeMeta')

def extractCommitConsistencyTest : IOExtractor := fun stt => do
  withExceptOkIO "Committing succeeds"
      (← commit stt.env.anonHashes stt.storeAnon true false)
    fun (stt, _) => -- TODO: also typecheck
      return test "consts and commits have consistent keys"
        (stt.consts.keysArray == stt.commits.keysArray)

section AnonHashGroups

/-
This section defines an extractor that consumes a list of groups of names and
creates tests that assert that:
1. Each pair of constants in the same group has the same anon hash
2. Each pair of constants in different groups has different anon hashes
-/

def extractAnonGroups (groups : List (List Name)) (stt : ContAddrState) :
    Except String (Array (Array $ Name × Hash)) := Id.run do
  let mut notFound : Array Name := #[]
  let mut hashGroups : Array (Array $ Name × Hash) := #[]
  for group in groups do
    let mut hashGroup : Array (Name × Hash) := #[]
    for name in group do
      match stt.env.consts.find? name with
      | none        => notFound  := notFound.push name
      | some (h, _) => hashGroup := hashGroup.push (name, h)
    hashGroups := hashGroups.push hashGroup
  if notFound.isEmpty then
    return .ok hashGroups
  else
    return .error s!"Not found: {", ".intercalate $ notFound.data.map toString}"

def extractAnonCidGroupsTests (groups : List $ List Name) : Extractor := fun stt =>
  withExceptOk "All constants can be found" (extractAnonGroups groups stt)
    fun anonGroups =>
      let anonEqTests := anonGroups.foldl (init := .done) fun tSeq anonGroup =>
        anonGroup.data.pairwise.foldl (init := tSeq) fun tSeq (x, y) =>
          tSeq ++ test s!"{x.1}ₐₙₒₙ = {y.1}ₐₙₒₙ" (x.2 == y.2)
      anonGroups.data.pairwise.foldl (init := anonEqTests) fun tSeq (g, g') =>
        (g.data.cartesian g'.data).foldl (init := tSeq) fun tSeq (x, y) =>
          tSeq ++ test s!"{x.1}ₐₙₒₙ ≠ {y.1}ₐₙₒₙ" (x.2 != y.2)

end AnonHashGroups
