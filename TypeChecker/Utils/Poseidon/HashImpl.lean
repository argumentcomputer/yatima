prelude
import TypeChecker.Utils.Poseidon.Hash

/-!
# Hash implementation

This module contains the primary function `Poseidon.hash` which

The inputs to `Poseidon.hash` are
* `HashProfile` : Contains the parameters prime `p`, width `t`, security parameters `M`, and S-box exponent `a`
* `Hash.Context` : Contains the necessary parameters to compute the Poseidon hash, in particular
  the MDS matrix and the array of round constants.
* `Array (Zmod profile.p)` : The message to hash. If the length of the array does not match the specified arity
  a dummy value of `0` is returned
* `Domain` : The domain in which to hash the function. Right now it is either a fixed-arity Merkle tree hash
  or fixed length input

Pre-computed profiles and contexts are available in the `Poseidon.Parameters` folder.
-/

namespace Poseidon

/--
These are the two domains specified in the Filecoin/Lurk implementation of Poseidon, and do not
constitute of all the possible domains.
-/
inductive Domain
  | merkleTree   -- Hashing fixed `arity : Nat` merkle tree`
  | fixedLength  -- Hashing fixed length inputs

/--
Prepares the preimage to serve as an input to the Poseidon hash function by prepending the domain
tag and padding when necessary
-/
def getInput (prof : HashProfile)
             (preimage : Array (Zmod prof.p))
             (domain : Domain) : Option $ Array $ Zmod prof.p :=
  match domain with
    | .merkleTree =>
      if preimage.size != prof.t - 1 then none else
        let domainTag : Zmod prof.p := ⟨.ofNat $ 2^(preimage.size) -1⟩
        some $ #[domainTag] ++ preimage
    | .fixedLength  =>
      if preimage.size > prof.t - 1 then none else
        let domainTag : Zmod prof.p := ⟨.ofNat $ 2^64 * preimage.size⟩
        let padding : Array $ Zmod prof.p := .mkArray (prof.t - 1 - preimage.size) 0
        some $ #[domainTag] ++ preimage ++ padding

/--
The primary hash function to be used to hash a preimage of the appropriate size. The second component
of the output vector is selected and returned (according to the Filecoin specification).

If the input size is mis-matched with the expected arity, then the hash returns a dummy value `0`.
-/
def hash (prof : HashProfile)
         (context : Hash.Context prof)
         (preimage : Array (Zmod prof.p))
         (domain : Domain) : Zmod prof.p :=
  let input? := getInput prof preimage domain
  match input? with
    | none       => 0
    | some input => hashInputWithCtx prof context input |>.get! 1
