import Yatima.Datatypes.Store
import Yatima.Typechecker.Extractor.ExtractError
import YatimaStdLib.Ord

namespace Yatima.Extractor

open Std (RBMap)

/--
`RecrCtx` contains information for the reconstruction of (mutual) definitions
and inductives. Each item (identified by an index) in the recursive context is
mapped to its constant index and its name. In the case of definitions, the items
are also identified by a second index that indicates their position among weakly
equal definitions.
-/
abbrev RecrCtx := RBMap (Nat × Option Nat) (Nat × Name) compare

/--
The reader structure for the `ExtractM` monad contains:
* `store`, which has the initial data of constants to be extracted
* `recrCtx` of type `RecrCtx`
* `bindDepth`, which says how many `lam`, `pi` or `letE` binders we've gone
through recursively; used to implement constant replacement of free variables
-/
structure ExtractEnv where
  store     : IR.Store
  recrCtx   : RecrCtx
  bindDepth : Nat
  deriving Inhabited

/-- Starts a new `ExtractEnv` with a given `Yatima.IR.Store` -/
def ExtractEnv.init (store : IR.Store) : ExtractEnv :=
  ⟨store, default, 0⟩

/--
Contains the progress of the extraction process.

* `univCache` and `constCache` are optimization means
* `tcStore` is the actual output of the extraction, whose order is pre-encoded based on the store
* `constsIdx` contains auxiliary data to recover a constant index by its name using the order in `consts`
-/
structure ExtractState where
  univCache  : RBMap IR.BothUnivCid TC.Univ compare
  constCache : RBMap IR.BothConstCid TC.ConstIdx compare
  tcStore    : TC.Store
  constsIdx  : RBMap Name TC.ConstIdx compare
  deriving Inhabited

/-- The monad in which extraction takes place -/
abbrev ExtractM := ReaderT ExtractEnv $ EStateM ExtractError ExtractState

/-- Runs a function in `ExtractM` given a `ExtractEnv` and a `ExtractState` -/
def ExtractM.run (env : ExtractEnv) (ste : ExtractState) (m : ExtractM α) :
    Except ExtractError ExtractState :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ stt  => .ok stt
  | .error e _ => .error e

/-- Extracts `x` from `some x` and throws an error otherwise -/
def ExtractM.unwrap : Option α → ExtractM α :=
  Option.option (throw .irError) pure

/-- Runs a computation with `bindDepth` reset to `0` -/
def withResetBindDepth : ExtractM α → ExtractM α :=
  withReader $ fun e => { e with bindDepth := 0 }

/-- Runs a computation with a certain `RecrCtx` -/
def withRecrs (recrCtx : RecrCtx) : ExtractM α → ExtractM α :=
  withReader $ fun e => { e with recrCtx }

/-- Runs a computation with `bindDepth` increased by `1` -/
def withNewBind : ExtractM α → ExtractM α :=
  withReader $ fun e => { e with bindDepth := e.bindDepth + 1 }

end Yatima.Extractor
