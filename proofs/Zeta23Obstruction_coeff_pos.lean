/-
# Damage Cost Exponent Law
Category: Brockian Corpus
Target: Zeta23Obstruction.damage_cost_exponent_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Zeta23Obstruction

/-- The coefficient `4π(A-1)` is strictly positive when the bandwidth `A` exceeds `1`. -/
theorem coeff_pos {A : ℝ} (hA : 1 < A) : 0 < 4 * Real.pi * (A - 1) :=
  mul_pos (by positivity) (by linarith)

/--
**Damage Cost Exponent Law.**
For any bandwidth `A > 1`, the rescaled deep-pair damage/cost ratio
`y ↦ exp (4π(A-1) y)` is strictly increasing and unbounded above.
-/
theorem damage_cost_exponent_law {A : ℝ} (hA : 1 < A) :
    StrictMono (fun y : ℝ => Real.exp (4 * Real.pi * (A - 1) * y)) ∧
      ∀ C : ℝ, 0 < C → ∃ y : ℝ, 0 < y ∧ Real.exp (4 * Real.pi * (A - 1) * y) > C := by
  have hc : 0 < 4 * Real.pi * (A - 1) := coeff_pos hA
  refine ⟨Real.exp_strictMono.comp (strictMono_mul_left_of_pos hc), ?_⟩
  intro C hC
  refine ⟨(|Real.log C| + 1) / (4 * Real.pi * (A - 1)), ?_, ?_⟩
  · exact div_pos (by positivity) hc
  · rw [mul_div_cancel₀ _ (ne_of_gt hc)]
    calc C = Real.exp (Real.log C) := (Real.exp_log hC).symm
      _ < Real.exp (|Real.log C| + 1) :=
          Real.exp_lt_exp.mpr (by have := le_abs_self (Real.log C); linarith)

end Zeta23Obstruction

