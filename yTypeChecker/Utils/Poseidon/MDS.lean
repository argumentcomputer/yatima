prelude
import yTypeChecker.Utils.YSL.Matrix
import yTypeChecker.Utils.YSL.ZMod

/-!
# Generates the Poseidon MDS Matrix

This module contains the basic functionality to generate the MDS matrix used in the Filecoin/Lurk
implementation of the Poseidon hash function

TODO : Add more MDS matrix generation paradigms, and add security tests for generated matrices.
-/

namespace Poseidon

/--
Generates an `t × t` Cauchy matrix over `Zmod p` with `i, j` entry `(i + t + j)⁻¹`.
This is the matrix  used as the MDS matrix for Filecoin.
-/
def generatePoseidonMDS (p t : Nat) : Matrix (Zmod p) := Id.run do
  let mut answer : Matrix (Zmod p) := #[]
  for c in [0 : t] do
    answer := answer.push #[]
    for r in [t : 2*t] do
      answer := answer.set! (answer.size - 1) (answer[answer.size - 1]!.push <| Zmod.modInv (r + c))
  return answer
