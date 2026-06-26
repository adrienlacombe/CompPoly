/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Lacombe
-/

import CompPoly.Fields.Mersenne

/-!
# Mersenne31 Field Tests

Small regression checks for the Mersenne31 concrete field surface.
-/

example : Fact (Nat.Prime Mersenne31.fieldSize) := inferInstance

example : Field Mersenne31.Field := inferInstance

example : NonBinaryField Mersenne31.Field := inferInstance

example : (2 : Mersenne31.Field) ≠ 0 := by
  exact NonBinaryField.char_neq_2

example : Mersenne31.fieldSize - 1 = 2 * (2 ^ (Mersenne31.pBits - 1) - 1) :=
  Mersenne31.fieldSize_sub_one
