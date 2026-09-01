import Mathlib
open Finset
namespace Frontier.AnalysisCalculus

theorem am_gm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a*b) ≤ (a+b)/2 := by
  rw [show (a+b)/2 = Real.sqrt (((a+b)/2)^2) by rw [Real.sqrt_sq (by linarith)]]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (a-b)]

theorem bernoulli (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n :=
  one_add_mul_le_pow (by linarith) n

theorem qm_am {n : ℕ} (a : Fin n → ℝ) : (∑ i, a i) ^ 2 ≤ n * ∑ i, (a i)^2 := by
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)

end Frontier.AnalysisCalculus

