import Mathlib

/-!
# Quadruplet 11 13 17 19
Category: Frontier — Prime Numbers
Target: Constellation.quadruplet_11_13_17_19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Constellation

/-- `(11, 13, 17, 19)` is a prime quadruplet with pattern `(0, 2, 6, 8)`:
each of `11, 13, 17, 19` is prime, and the offsets from `11` are `0, 2, 6, 8`. -/
theorem quadruplet_11_13_17_19 :
    Nat.Prime 11 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧ Nat.Prime 19 ∧
      13 = 11 + 2 ∧ 17 = 11 + 6 ∧ 19 = 11 + 8 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, rfl, rfl, rfl⟩

end Constellation

