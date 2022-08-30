import Yatima.Datatypes.Store
import Yatima.Compiler.Utils
import Yatima.Converter.ConvertError
import YatimaStdLib.RBMap

namespace Yatima

namespace Converter

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
The reader structure for the `ConvertM` monad contains:
* `store`, which has the initial data of constants to be extracted
* `recrCtx` of type `RecrCtx`
* `bindDepth`, which says how many `lam`, `pi` or `letE` binders we've gone
through recursively; used to implement constant replacement of free variables
-/
structure ConvertEnv where
  store     : Ipld.Store
  recrCtx   : RecrCtx
  bindDepth : Nat
  deriving Inhabited

/-- Starts a new `ConvertEnv` with a given `Yatima.Ipld.Store` -/
def ConvertEnv.init (store : Ipld.Store) : ConvertEnv :=
  ⟨store, default, 0⟩

/--
Contains the progress of the conversion process.

* `univ_cache` and `const_cache` are optimization means
* `consts` is the actual output of the conversion, whose order is pre-encoded based on the store
* `constsIdx` contains auxiliary data to recover a constant index by its name using the order in `consts`
-/
structure ConvertState where
  univ_cache  : RBMap UnivCid Univ compare
  const_cache : RBMap ConstCid ConstIdx compare
  consts      : Array Const
  constsIdx   : RBMap Name ConstIdx compare
  deriving Inhabited

/-- The monad in which conversion takes place -/
abbrev ConvertM := ReaderT ConvertEnv $ EStateM ConvertError ConvertState

/-- Runs a function in `ConvertM` given a `ConvertEnv` and a `ConvertState` -/
def ConvertM.run (env : ConvertEnv) (ste : ConvertState) (m : ConvertM α) :
    Except ConvertError ConvertState :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ stt  => .ok stt
  | .error e _ => .error e

/-- Extracts `x` from `some x` and throws an error otherwise -/
def ConvertM.unwrap : Option α → ConvertM α :=
  Option.option (throw .ipldError) pure

/-- Runs a computation with `bindDepth` reset to `0` -/
def withResetBindDepth : ConvertM α → ConvertM α :=
  withReader $ fun e => { e with bindDepth := 0 }

/-- Runs a computation with a certain `RecrCtx` -/
def withRecrs (recrCtx : RecrCtx) : ConvertM α → ConvertM α :=
  withReader $ fun e => { e with recrCtx }

/-- Runs a computation with `bindDepth` increased by `1` -/
def withNewBind : ConvertM α → ConvertM α :=
  withReader $ fun e => { e with bindDepth := e.bindDepth + 1 }

namespace Converter

namespace Yatima
