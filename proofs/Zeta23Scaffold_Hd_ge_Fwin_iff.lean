/-
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- The window function `H(λ) = 2 - 1/λ - λ/3`. -/
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- `H_d(λ) = (1 + H(λ))/2`. -/
noncomputable def Hd (lam : ℝ) : ℝ := (1 + Hwin lam) / 2

/-- `F(λ) = λ / (1 + λ²/3)`. -/
noncomputable def Fwin (lam : ℝ) : ℝ := lam / (1 + lam ^ 2 / 3)

/-- Clearing denominators: `3λ · H(λ) = 6λ - 3 - λ²` for `λ ≠ 0`. -/
theorem Hwin_mul (lam : ℝ) (hlam : lam ≠ 0) :
    Hwin lam * (3 * lam) = 6 * lam - 3 - lam ^ 2 := by
  unfold Hwin
  field_simp
  ring

/-- Key algebraic identity: for `λ > 0`,
`H_d(λ) - F(λ) = (6λ - 3 - λ²)(λ² - 3λ + 3) / (6λ(3 + λ²))`. -/
theorem Hd_sub_Fwin_eq (lam : ℝ) (hlam : 0 < lam) :
    Hd lam - Fwin lam =
      (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) / (6 * lam * (3 + lam ^ 2)) := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  have h2 : (0 : ℝ) < 3 + lam ^ 2 := by positivity
  have h3 : (0 : ℝ) < 1 + lam ^ 2 / 3 := by positivity
  unfold Hd Fwin Hwin
  field_simp
  ring

/-- Unconditional form: for every `λ > 0`, `F(λ) ≤ H_d(λ) ↔ 0 ≤ H(λ)`.
The auxiliary quadratic factor `λ² - 3λ + 3` has negative discriminant, hence is
positive, so the sign of `H_d(λ) - F(λ)` is exactly that of `6λ - 3 - λ² = 3λ·H(λ)`. -/
theorem Hd_ge_Fwin_iff_of_pos (lam : ℝ) (hlam : 0 < lam) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hq : 0 < lam ^ 2 - 3 * lam + 3 := by nlinarith [sq_nonneg (2 * lam - 3)]
  have hden : 0 < 6 * lam * (3 + lam ^ 2) := by positivity
  have hH : 0 ≤ Hwin lam ↔ 0 ≤ 6 * lam - 3 - lam ^ 2 := by
    rw [← Hwin_mul lam (ne_of_gt hlam)]
    exact (mul_nonneg_iff_of_pos_right (by positivity : (0:ℝ) < 3 * lam)).symm
  rw [← sub_nonneg, Hd_sub_Fwin_eq lam hlam, le_div_iff₀ hden, hH]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0`, for `0 < λ ≤ 1`
(preprint eq. (1.3), third line, first equivalence).

The hypothesis `lam ≤ 1` is included as requested, but it is not needed: see
`Hd_ge_Fwin_iff_of_pos`, which gives the same equivalence for all `λ > 0`. -/
theorem Hd_ge_Fwin_iff (lam : ℝ) (hlam : 0 < lam) (_hlam1 : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam :=
  Hd_ge_Fwin_iff_of_pos lam hlam

end Zeta23Scaffold

