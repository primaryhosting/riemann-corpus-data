import Mathlib

/-!
# Rank Trace C General
Category: Riemann Program
Target: Riemann.method.rank_trace_c_general
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

namespace Riemann
namespace method

/-- Scalar core of the general-`c` rank-trace inequality (Lemma 3.2): for all real `x` and `c`,
`2*c*x - c^2 ≤ x^2`, with equality exactly when `x = c`. -/
theorem rank_trace_c_general (x c : ℝ) :
    2 * c * x - c ^ 2 ≤ x ^ 2 ∧ (2 * c * x - c ^ 2 = x ^ 2 ↔ x = c) := by
  have hsq : (0:ℝ) ≤ (x - c) ^ 2 := sq_nonneg _
  refine ⟨by nlinarith, ⟨fun h => ?_, fun h => by subst h; ring⟩⟩
  have hz : (x - c) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
  linarith

end method
end Riemann

