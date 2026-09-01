import Mathlib
/-!
# Tent Combination Neg On Band
Category: Brockian Corpus
Target: Zeta23Obstruction.tent_combination_neg_on_band
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Obstruction

/-- The tent profile `T a = max 0 (1 - |a|)`. -/
noncomputable def T : ℝ → ℝ := fun a => max 0 (1 - |a|)

/-- On the band `(1, 5/2)`, the tent combination
`T a - (1/20) * (T (a - 3/2) + T (a + 3/2))` is strictly negative. -/
theorem tent_combination_neg_on_band (a : ℝ) (h1 : 1 < a) (h2 : a < 5 / 2) :
    T a - (1 / 20) * (T (a - 3 / 2) + T (a + 3 / 2)) < 0 := by
  have habs : |a| = a := abs_of_pos (by linarith)
  have hTa : T a = 0 := by
    simp only [T, habs, max_eq_left_iff]
    linarith
  have hshift : |a - 3 / 2| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hTm : 0 < T (a - 3 / 2) := by
    have h : (0:ℝ) < 1 - |a - 3 / 2| := by linarith
    simpa [T] using h
  have hTp : 0 ≤ T (a + 3 / 2) := le_max_left _ _
  rw [hTa]
  linarith

end Zeta23Obstruction

