import Mathlib

/-!
# Damage Cost Exponent Law
Category: Brockian Corpus
Target: Zeta23Obstruction.damage_cost_exponent_law
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

namespace Zeta23Obstruction

/-- The rescaled deep-pair damage/cost ratio `y ↦ exp (4π(A-1)y)` is strictly increasing
and unbounded above, for any bandwidth `A > 1`. -/
theorem damage_cost_exponent_law {A : ℝ} (hA : 1 < A) :
    StrictMono (fun y : ℝ => Real.exp (4 * Real.pi * (A - 1) * y)) ∧
      ∀ C : ℝ, 0 < C → ∃ y : ℝ, 0 < y ∧ Real.exp (4 * Real.pi * (A - 1) * y) > C := by
  have hpos : 0 < 4 * Real.pi * (A - 1) := by
    have : (0:ℝ) < A - 1 := by linarith
    positivity
  constructor
  · intro a b hab
    exact Real.exp_lt_exp.mpr (by nlinarith)
  · intro C hC
    refine ⟨max 1 ((Real.log C + 1) / (4 * Real.pi * (A - 1))), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
    have hle : (Real.log C + 1) / (4 * Real.pi * (A - 1)) ≤
        max 1 ((Real.log C + 1) / (4 * Real.pi * (A - 1))) := le_max_right _ _
    have hkey : Real.log C + 1 ≤ 4 * Real.pi * (A - 1) *
        max 1 ((Real.log C + 1) / (4 * Real.pi * (A - 1))) := by
      rw [← div_le_iff₀' hpos]
      exact hle
    calc C = Real.exp (Real.log C) := (Real.exp_log hC).symm
      _ < Real.exp (Real.log C + 1) := Real.exp_lt_exp.mpr (by linarith)
      _ ≤ _ := Real.exp_le_exp.mpr hkey

end Zeta23Obstruction

