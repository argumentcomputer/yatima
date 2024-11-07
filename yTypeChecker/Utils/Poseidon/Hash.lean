prelude
import yTypeChecker.Utils.Poseidon.Profile
import yTypeChecker.Utils.Poseidon.MDS
import yTypeChecker.Utils.Poseidon.RoundConstants
import yTypeChecker.Utils.YSL.ZMod
import yTypeChecker.Utils.YSL.Matrix
import yTypeChecker.Utils.YSL.Monad

/-!
# The Poseidon hashing algorithm

This module contains the core hashing logic used to produce Poseidon hashes.

A hash is done in the context of a `HashProfile` which has the information of the basefield prime,
security level, width, and other constants. See `Poseidon.Profile` for a full description.

The main function is `hashInput`, but most users will find the `Poseidon.hash` in `Poseidon.HashImpl`
to be the more useful method.
-/

namespace Poseidon

/--
A context in which to perform the Poseidon Hash. A hashing context requires an MDS matrix for the
linear layers, and an array of round constants `roundConst` for the ARC layer.

The context can be generated from a HashProfile with some choices, but is not determined by it so
they are separated to allow for alternate implementations.
-/
structure Hash.Context (profile : HashProfile) where
  mdsMatrix : Matrix (Zmod profile.p)
  roundConst : Array (Zmod profile.p)

open Hash in
/--
This function generates a context from a Hash profile according to the Filecoin specifications for
the MDS matrix and round constants
-/
def HashProfile.genericCtx (profile : HashProfile) : Context profile where
  mdsMatrix := generatePoseidonMDS profile.p profile.t
  roundConst := generateRConstants false profile

namespace Hash

/--
The internal state for the hashing algorithm
-/
structure State (profile : HashProfile) where
  round : Nat
  state : Vector (Zmod profile.p)

def initialState {profile : HashProfile} (input : Vector (Zmod profile.p)) : State profile := ⟨0, input⟩

end Hash

open Hash in
/--
The Monad in which the hashing is performed
-/
abbrev HashM (profile : HashProfile) := ReaderT (Context profile) $ StateM (State profile)

variable (profile : HashProfile)

namespace HashM

open Matrix in
def linearLayer : HashM profile PUnit := do
  let mds := (← read).mdsMatrix
  modify (fun ⟨r, vec⟩ => ⟨r, action mds vec⟩)

def addConst : HashM profile PUnit := do
  let t := profile.t
  let round := (← get).round
  let const := (← read).roundConst.extract (t * round) (t * round + t)
  modify fun ⟨r, vec⟩ => ⟨r, vec + const⟩

def fullRound : HashM profile PUnit :=
  addConst profile *>
  (modify fun ⟨r, vec⟩ => ⟨r.succ, vec.map profile.sBox⟩) *>
  linearLayer profile

def partialRound : HashM profile PUnit :=
  addConst profile *>
  (modify fun ⟨r, vec⟩ => ⟨r.succ, vec.set! 0 (profile.sBox vec[0]!)⟩) *>
  linearLayer profile

open Monad in
def runRounds : HashM profile PUnit :=
  repeatM (fullRound profile) (profile.fullRounds / 2) *>
  repeatM (partialRound profile) (profile.partRounds) *>
  repeatM (fullRound profile) (profile.fullRounds / 2)

open Hash in
/--
Runs all the rounds needed for the hashing algorithm and extracts the final state.
-/
def hash (context : Context profile) (input : Vector (Zmod profile.p)) : State profile :=
  Prod.snd <$> StateT.run (ReaderT.run (runRounds profile) context) (initialState input)

end HashM

open Hash

/--
Validates the input vector and context before feeding them to the Hash function to avoid runtime
panics.

TODO : Add more validation to reduce the junk values being returned for bad inputs
-/
def validateInputs (context : Context profile)  (input : Vector (Zmod profile.p)) : Bool :=
  input.size == profile.t &&
  context.roundConst.size == profile.t * (profile.fullRounds + profile.partRounds) &&
  profile.t == context.mdsMatrix.size &&
  profile.t == context.mdsMatrix.transpose.size

/--
A wraper around `HashM.hash` which extracts only the final vector of outputs.

If the input is invalid according to `validateInputs` then a junk empty array is returned.
-/
def hashInputWithCtx (context : Context profile) (input : Vector (Zmod profile.p)) : Vector (Zmod profile.p) :=
  if validateInputs profile context input then (HashM.hash profile context input).state else #[]

/--
Hashes the input where the context is taken to be generated from the Profile.

Note: This will be slower than `hashInputWithCtx` as the context has to be generated every time,
so it is advised to use pre-computed contexts available in the `Poseidon.Parameters` folder.
-/
def hashInput (input : Vector (Zmod profile.p)) : Vector (Zmod profile.p) :=
  let context := profile.genericCtx
  hashInputWithCtx profile context input

end Poseidon
