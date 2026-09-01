import Mathlib
open Finset
namespace MS2.Prob2

/-- AM–GM for three nonnegative reals. -/
theorem am_gm_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a*b*c)^((1:ℝ)/3) ≤ (a+b+c)/3 := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := 1/3) (w₂ := 1/3) (w₃ := 1/3) (p₁ := a) (p₂ := b) (p₃ := c)
    (by norm_num) (by norm_num) (by norm_num) ha hb hc (by norm_num)
  calc (a*b*c)^((1:ℝ)/3) = a^((1:ℝ)/3) * b^((1:ℝ)/3) * c^((1:ℝ)/3) := by
        rw [Real.mul_rpow (mul_nonneg ha hb) hc, Real.mul_rpow ha hb]
    _ ≤ 1/3 * a + 1/3 * b + 1/3 * c := h
    _ = (a+b+c)/3 := by ring

/-- The two-element rearrangement inequality. -/
theorem rearrangement_two (a1 a2 b1 b2 : ℝ) (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    a1*b2 + a2*b1 ≤ a1*b1 + a2*b2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

/-- A sum of squares of reals is nonnegative. -/
theorem sum_squares_nonneg {n : ℕ} (a : Fin n → ℝ) : 0 ≤ ∑ i, (a i)^2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg (a i)

/-- The triangle inequality for finite sums. -/
theorem triangle_sum {n : ℕ} (a : Fin n → ℝ) : |∑ i, a i| ≤ ∑ i, |a i| :=
  Finset.abs_sum_le_sum_abs a Finset.univ

/-- Cauchy–Schwarz / QM–AM: `(∑ aᵢ)² ≤ n ∑ aᵢ²`.
The nonnegativity hypothesis `ha` is not needed for this inequality, but it is kept
since it was part of the requested statement. -/
theorem qm_am_general {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i)^2 ≤ n * ∑ i, (a i)^2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := a)
  simpa using h

end MS2.Prob2

