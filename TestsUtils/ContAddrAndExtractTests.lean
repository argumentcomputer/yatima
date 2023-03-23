import LSpec
import Yatima.ContAddr.ContAddr
import Yatima.Typechecker.Typechecker
import Yatima.Common.GenTypechecker
import Lurk.Eval

open LSpec Yatima IR ContAddr Typechecker
open System (FilePath)

-- Move to LSpec
@[specialize]
def withExceptOkM [Monad m] (descr : String) (exc : Except ε α) [ToString ε]
    (f : α → m TestSeq) : m TestSeq :=
  match exc with
  | .error e => return test descr (ExpectationFailure "ok _" s!"error {e}")
  | .ok    a => return test descr true $ ← f a

abbrev Extractor := ContAddrState → TestSeq
abbrev IOExtractor := ContAddrState → IO TestSeq

/-- Run tests from extractors given a Lean source file -/
def ensembleTestExtractors (source : FilePath)
  (extractors : List Extractor) (ioExtractors : List IOExtractor)
    (setPaths quick : Bool := true) : IO TestSeq := do
  if setPaths then Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend (← IO.FS.readFile source) source
  let (constMap, delta) := leanEnv.getConstsAndDelta
  withExceptOkM s!"Content-addresses {source}"
      (← contAddr constMap delta quick false) fun stt => do
    let pureTests := extractors.foldl (init := .done)
      fun acc ext => acc ++ (ext stt)
    ioExtractors.foldlM (init := pureTests) fun acc ext =>
      do pure $ acc ++ (← ext stt)

/-- Calls `ensembleTestExtractors` for multiple sources -/
def ensembleTestExtractors' (sources : List FilePath)
  (extractors : List Extractor) (ioExtractors : List IOExtractor)
    (setPaths : Bool := true) : IO TestSeq :=
  sources.foldlM (init := .done) fun acc source => do
    let g := group s!"Tests for {source}" $
      ← ensembleTestExtractors source extractors ioExtractors setPaths
    pure $ acc ++ g

/-- Asserts that all constants typechecks -/
def extractTypecheckingTests : Extractor := fun stt =>
  withExceptOk "Typechecking succeeds" (typecheckAll stt.store stt.env.constNames)
    fun _ => .done

/-- Asserts that some constant doesn't typecheck -/
def extractNonTypecheckingTests : Extractor := fun stt =>
  withExceptError "Typechecking fails" (typecheckAll stt.store stt.env.constNames)
    fun _ => .done

section AnonHashGroups

/-
This section defines an extractor that consumes a list of groups of names and
creates tests that assert that:
1. Each pair of constants in the same group has the same anon hash
2. Each pair of constants in different groups has different anon hashes
-/

def extractAnonGroups (groups : List (List Name)) (stt : ContAddrState) :
    Except String (Array (Array $ Name × Lurk.F)) := Id.run do
  let mut notFound : Array Name := #[]
  let mut hashGroups : Array (Array $ Name × Lurk.F) := #[]
  for group in groups do
    let mut hashGroup : Array (Name × Lurk.F) := #[]
    for name in group do
      match stt.env.consts.find? name with
      | none   => notFound  := notFound.push name
      | some h => hashGroup := hashGroup.push (name, h)
    hashGroups := hashGroups.push hashGroup
  if notFound.isEmpty then
    return .ok hashGroups
  else
    return .error s!"Not found: {", ".intercalate $ notFound.data.map toString}"

def extractAnonGroupsTests (groups : List $ List Name) : Extractor := fun stt =>
  withExceptOk "All constants can be found" (extractAnonGroups groups stt)
    fun anonGroups =>
      let anonEqTests := anonGroups.foldl (init := .done) fun tSeq anonGroup =>
        anonGroup.data.pairwise.foldl (init := tSeq) fun tSeq (x, y) =>
          tSeq ++ test s!"{x.1}ₐₙₒₙ = {y.1}ₐₙₒₙ" (x.2 == y.2)
      anonGroups.data.pairwise.foldl (init := anonEqTests) fun tSeq (g, g') =>
        (g.data.cartesian g'.data).foldl (init := tSeq) fun tSeq (x, y) =>
          tSeq ++ test s!"{x.1}ₐₙₒₙ ≠ {y.1}ₐₙₒₙ" (x.2 != y.2)

end AnonHashGroups

section LurkTypechecking

open Lurk.Expr.DSL Lurk.Value in
def extractLurkTypecheckTests (decls : List Name) : IOExtractor := fun stt => do
  withExceptOkM "Typechecker compiles" (← genTypechecker) fun tcExpr =>
    let env := stt.env
    return withExceptOk "Store extraction succeeds"
        (stt.ldonHashState.extractComms env.hashes) fun store =>
      decls.foldl (init := .done) fun tSeq decl => tSeq ++
        withOptionSome s!"{decl} hash is found" (env.consts.find? decl) fun hash =>
          let expr := Lurk.Expr.app tcExpr ⟦$hash⟧
          withExceptOk s!"Typechecking {decl} succeeds" (expr.evaluate' store) fun v =>
            test s!"{decl} typechecks" (v == ⦃("Bool" 1)⦄)

end LurkTypechecking
