/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CompPoly.Fields.Basic
import CompPoly.Fields.PrattCertificate

/-!
  # Mersenne prime field `2^{31} - 1`

  This is the field used in Circle STARKs.
-/

namespace Mersenne31

/-- The Mersenne31 field modulus, `2^31 - 1`. -/
@[reducible]
def fieldSize : Nat := 2 ^ 31 - 1

/-- The Mersenne31 prime field as a `ZMod`. -/
abbrev Field := ZMod fieldSize

/-- The Mersenne31 modulus is prime. -/
theorem is_prime : Nat.Prime fieldSize := by
  unfold fieldSize
  pratt

/-!
  ## Constants

  These are convenience constants for the Mersenne31 field:
  - `pBits = 31`
  - `twoAdicity = 1` with `fieldSize - 1 = 2^1 * (2^30 - 1)`
-/

/-- Bit width of the Mersenne31 modulus. -/
@[reducible]
def pBits : Nat := 31

/-- The largest supported power-of-two root-of-unity exponent for Mersenne31. -/
@[reducible]
def twoAdicity : Nat := 1

instance : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩

instance : _root_.Field Field := ZMod.instField fieldSize

instance : NonBinaryField Field where
  char_neq_2 := by
    simpa [Field, fieldSize] using
      (by decide : (2 : ZMod (2 ^ 31 - 1)) ≠ 0)

/-!
  ## Two-adicity and modulus facts

  We record the factorization of `fieldSize - 1`, which is useful for downstream
  domain and root-of-unity work.
-/

/-- The Mersenne31 modulus is positive. -/
lemma fieldSize_pos : 0 < fieldSize := by
  norm_num [fieldSize]

/-- The Mersenne31 modulus is nonzero. -/
lemma fieldSize_ne_zero : fieldSize ≠ 0 :=
  Nat.ne_of_gt fieldSize_pos

/-- The factorization `fieldSize - 1 = 2^twoAdicity * (2^30 - 1)`. -/
lemma fieldSize_sub_one_factorization :
    fieldSize - 1 = 2 ^ twoAdicity * (2 ^ (pBits - 1) - 1) := by
  unfold fieldSize twoAdicity pBits
  decide

end Mersenne31
