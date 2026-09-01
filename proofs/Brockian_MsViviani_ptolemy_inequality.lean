import Mathlib
namespace Brockian.MsViviani

/-- The inversion map `x ↦ ‖x‖⁻² • x` scales distances by `(‖x‖ * ‖y‖)⁻¹`. -/
private lemma norm_inversion_sub_inversion {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖(‖x‖ ^ 2)⁻¹ • x - (‖y‖ ^ 2)⁻¹ • y‖ = ‖x - y‖ / (‖x‖ * ‖y‖) := by
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hxy : ‖x‖ * ‖y‖ ≠ 0 := mul_ne_zero hx' hy'
  -- The key is to show ‖‖y‖² • x - ‖x‖² • y‖ = ‖x‖ * ‖y‖ * ‖x - y‖
  have key : ‖‖y‖ ^ 2 • x - ‖x‖ ^ 2 • y‖ = ‖x‖ * ‖y‖ * ‖x - y‖ := by
    have h1 : ‖‖y‖ ^ 2 • x - ‖x‖ ^ 2 • y‖ ^ 2 = (‖x‖ * ‖y‖ * ‖x - y‖) ^ 2 := by
      rw [norm_sub_sq_real]
      simp [norm_smul, inner_smul_left, inner_smul_right]
      nth_rw 2 [mul_pow, mul_pow]
      rw [norm_sub_sq_real]
      rw [real_inner_comm y x]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg y)) (norm_nonneg _))).mp h1
  -- Rewrite LHS using common factor
  have h2 : (‖x‖ ^ 2)⁻¹ • x - (‖y‖ ^ 2)⁻¹ • y = (‖x‖ ^ 2 * ‖y‖ ^ 2)⁻¹ • (‖y‖ ^ 2 • x - ‖x‖ ^ 2 • y) := by
    rw [smul_sub]
    congr 1
    · rw [smul_smul]
      field_simp
    · rw [smul_smul]
      field_simp
  rw [h2, norm_smul, key]
  have h3 : ‖(‖x‖ ^ 2 * ‖y‖ ^ 2)⁻¹‖ = (‖x‖ ^ 2 * ‖y‖ ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
  rw [h3]
  field_simp

/-- Ptolemy's inequality, vector form, in the case where all three vectors are nonzero. -/
private lemma ptolemy_vector_ne_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ‖a - c‖ * ‖b‖ ≤ ‖a - b‖ * ‖c‖ + ‖b - c‖ * ‖a‖ := by
  have ha' : (0:ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have hb' : (0:ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hc' : (0:ℝ) < ‖c‖ := norm_pos_iff.mpr hc
  -- triangle inequality for the inverted points
  have htri : ‖(‖a‖ ^ 2)⁻¹ • a - (‖c‖ ^ 2)⁻¹ • c‖ ≤
      ‖(‖a‖ ^ 2)⁻¹ • a - (‖b‖ ^ 2)⁻¹ • b‖ + ‖(‖b‖ ^ 2)⁻¹ • b - (‖c‖ ^ 2)⁻¹ • c‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [norm_inversion_sub_inversion a c ha hc, norm_inversion_sub_inversion a b ha hb,
    norm_inversion_sub_inversion b c hb hc] at htri
  -- multiply through by ‖a‖ * ‖b‖ * ‖c‖
  have hmul := mul_le_mul_of_nonneg_left htri
    (le_of_lt (mul_pos (mul_pos ha' hb') hc'))
  calc ‖a - c‖ * ‖b‖
      = ‖a‖ * ‖b‖ * ‖c‖ * (‖a - c‖ / (‖a‖ * ‖c‖)) := by field_simp
    _ ≤ ‖a‖ * ‖b‖ * ‖c‖ * (‖a - b‖ / (‖a‖ * ‖b‖) + ‖b - c‖ / (‖b‖ * ‖c‖)) := hmul
    _ = ‖a - b‖ * ‖c‖ + ‖b - c‖ * ‖a‖ := by field_simp

/-- Ptolemy's inequality, vector form: for `a b c` in a real inner product space,
    `‖a - c‖ * ‖b‖ ≤ ‖a - b‖ * ‖c‖ + ‖b - c‖ * ‖a‖`. -/
private lemma ptolemy_vector {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) :
    ‖a - c‖ * ‖b‖ ≤ ‖a - b‖ * ‖c‖ + ‖b - c‖ * ‖a‖ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [mul_comm]
  rcases eq_or_ne b 0 with rfl | hb
  · simp; positivity
  rcases eq_or_ne c 0 with rfl | hc
  · simp [mul_comm]
  exact ptolemy_vector_ne_zero a b c ha hb hc

/-- Ptolemy's inequality: for any four points in an inner product space,
    dist A C · dist B D ≤ dist A B · dist C D + dist B C · dist A D. -/
theorem ptolemy_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B C D : E) :
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D := by
  have h := ptolemy_vector (A - D) (B - D) (C - D)
  simpa [dist_eq_norm, sub_sub_sub_cancel_right] using h

end Brockian.MsViviani

