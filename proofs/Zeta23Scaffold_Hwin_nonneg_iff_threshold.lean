/-
# Hwin Nonneg Iff Threshold
Category: A Assembly
Target: Zeta23Scaffold.Hwin_nonneg_iff_threshold
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- On `0 < λ ≤ 1`, `H(λ) ≥ 0` iff `λ ≥ 3 - √6`. -/
theorem Hwin_nonneg_iff_threshold (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 1) :
    0 ≤ Hwin lam ↔ 3 - Real.sqrt 6 ≤ lam := by
  have h6 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hlt : Real.sqrt 6 < 3 := by
    nlinarith [Real.sqrt_nonneg (6 : ℝ), h6]
  have hgt : 2 < Real.sqrt 6 := by
    nlinarith [Real.sqrt_nonneg (6 : ℝ), h6]
  have hinv : 1 / lam * lam = 1 := by field_simp
  unfold Hwin
  constructor
  · intro h
    nlinarith [h6, hinv, mul_pos hpos hpos]
  · intro h
    have key : lam ^ 2 - 6 * lam + 3 ≤ 0 := by nlinarith [h6]
    have : 0 ≤ (2 - 1 / lam - lam / 3) * (3 * lam) := by nlinarith [hinv]
    nlinarith [this, hpos]

end Zeta23Scaffold

