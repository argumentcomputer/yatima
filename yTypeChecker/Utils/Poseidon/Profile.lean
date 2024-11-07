prelude
import yTypeChecker.Utils.YSL.ZMod

/-!
# Poseidon Profiles

This module defines _Profiles_ used by the Poseidon hash function

A **security profile** consists of
* `M` : The number of bits that can be securely hashed
* `t` : The internal width of the hashing function
* `p` : The prime characteristic of the base field
* `a` : The s box exponent

A **hash profile** has the additional data of
* `fullRounds` : The number of full rounds the hash function runs with this profile
* `partRounds` : The number of partial rounds run the hash function runs with this profile
-/

namespace Poseidon

/--
The Poseidon security profile, contains data about secure bit lengths, width, primes, and s box exponent
-/
structure SecProfile where
  M : Nat -- Security
  t : Nat -- Internal capacity
  p : Nat -- Prime
  a : Int -- SBox exponent
deriving Repr

/--
The Poseidon hash profile, contains data about the number of full and partial rounds the Hash should run.
A minimally secure `HashProfile` can be derived from `SecProfile` using `SecProfile.hashProfile` found
in `Poseidon.RoundNumbers`.
-/
structure HashProfile extends SecProfile where
  fullRounds : Nat
  partRounds : Nat
deriving Repr

open Zmod in
def HashProfile.sBox (profile : HashProfile) : Zmod profile.p → Zmod profile.p :=
  match profile.a with
  | .ofNat n => fun x => x^n
  | .negSucc n => fun x => (.modInv x)^(n + 1)
