import Mathlib
open Finset
namespace Frontier.InformationTheory
theorem entropy_term_nonneg (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ - p * Real.log p := by
  rcases eq_or_lt_of_le h0 with h | h
  · simp [← h]
  · have hlog : Real.log p ≤ 0 := Real.log_nonpos h0 h1
    nlinarith

theorem cauchy_schwarz_finite {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, (a i)^2) * (∑ i, (b i)^2) :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b

theorem gibbs_nonneg {n : ℕ} (p q : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hsp : ∑ i, p i = 1) (hsq : ∑ i, q i = 1) : 0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have key : ∀ i : Fin n, p i - q i ≤ p i * Real.log (p i / q i) := by
    intro i
    have hpi := hp i
    have hqi := hq i
    have hlog : Real.log (q i / p i) ≤ q i / p i - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hqi hpi)
    have hmul : p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
      mul_le_mul_of_nonneg_left hlog hpi.le
    have hrw : p i * (q i / p i - 1) = q i - p i := by
      field_simp
    have hneg : Real.log (q i / p i) = - Real.log (p i / q i) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [hneg, hrw] at hmul
    linarith
  have hsum : ∑ i, (p i - q i) ≤ ∑ i, p i * Real.log (p i / q i) :=
    Finset.sum_le_sum (fun i _ => key i)
  rw [Finset.sum_sub_distrib, hsp, hsq] at hsum
  simpa using hsum

end Frontier.InformationTheory

