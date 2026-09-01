import Mathlib
open Finset
namespace MS2.IT2

theorem entropy_nonneg (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ -p * Real.log p := by
  have hlog : Real.log p ≤ 0 := Real.log_nonpos h0 h1
  nlinarith [mul_nonneg h0 (neg_nonneg.mpr hlog)]

theorem kraft_two_symbols (l : ℕ) : (2:ℝ)^(-(l:ℤ)) ≤ 1 := by
  apply zpow_le_one_of_nonpos₀ (by norm_num)
  simp

theorem log_sum_two (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (a*b) = Real.log a + Real.log b :=
  Real.log_mul ha.ne' hb.ne'

theorem uniform_max_entropy (n : ℕ) (hn : 0 < n) : -(1:ℝ) * Real.log (1/n) = Real.log n := by
  rw [Real.log_div one_ne_zero (by exact_mod_cast hn.ne')]
  simp

theorem exp_log_id (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x) = x := Real.exp_log hx

end MS2.IT2

