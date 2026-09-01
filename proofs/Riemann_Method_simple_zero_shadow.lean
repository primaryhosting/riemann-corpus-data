import Mathlib

/-!
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann.Method

/-- **Simple zero shadow.** For every natural number `m ≥ 1` we have `2 * m ≤ m ^ 2 + 1`,
with equality precisely when `m = 1`.  This is the integrality step `(m - 1) ^ 2 ≥ 0`. -/
theorem simple_zero_shadow (m : ℕ) (hm : 1 ≤ m) :
    2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [Nat.sub_add_cancel hm, sq_nonneg (m - 1)]
  · intro h; nlinarith [Nat.one_le_iff_ne_zero.mp hm]
  · rintro rfl; norm_num

end Riemann.Method

