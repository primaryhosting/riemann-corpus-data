import Mathlib
namespace Brockian.MsStewart

/-- Algebraic core of Stewart's theorem in an inner product space. -/
private lemma stewart_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (t : ℝ) :
    ‖u‖ ^ 2 * (1 - t) + ‖u - v‖ ^ 2 * t = ‖u - t • v‖ ^ 2 + t * (1 - t) * ‖v‖ ^ 2 := by
  norm_num [norm_sub_sq_real, norm_smul, real_inner_smul_right]
  rw [mul_pow, sq_abs]
  ring

/-- Stewart's theorem: for a point D on segment BC of a triangle,
    |AB|²·|DC| + |AC|²·|BD| = |BC|·(|AD|² + |BD|·|DC|). -/
theorem stewart (A B C D : EuclideanSpace ℝ (Fin 2)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hD : D = B + t • (C - B)) :
    dist A B ^ 2 * dist D C + dist A C ^ 2 * dist B D
      = dist B C * (dist A D ^ 2 + dist B D * dist D C) := by
  set u : EuclideanSpace ℝ (Fin 2) := A - B with hu
  set v : EuclideanSpace ℝ (Fin 2) := C - B with hv
  have hAB : dist A B = ‖u‖ := by rw [dist_eq_norm]
  have hAC : dist A C = ‖u - v‖ := by
    rw [dist_eq_norm, hu, hv]; congr 1; abel
  have hBC : dist B C = ‖v‖ := by rw [dist_comm, dist_eq_norm]
  have hBD : dist B D = t * ‖v‖ := by
    rw [dist_comm, dist_eq_norm, hD]
    have : B + t • (C - B) - B = t • v := by rw [hv]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hDC : dist D C = (1 - t) * ‖v‖ := by
    rw [dist_eq_norm, hD]
    have : B + t • (C - B) - C = (-(1 - t)) • v := by
      rw [hv, neg_smul, sub_smul, one_smul]; module
    rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
  have hAD : dist A D = ‖u - t • v‖ := by
    rw [dist_eq_norm, hD, hu, hv]; congr 1; abel
  rw [hAB, hAC, hBC, hBD, hDC, hAD]
  have := stewart_aux u v t
  nlinarith [this, norm_nonneg v]

end Brockian.MsStewart

