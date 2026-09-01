import Mathlib
open Finset
namespace C2.IT3

/-- Each entropy term `-p log p` is nonnegative on `[0,1]`. -/
theorem entropy_term_bound (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ -p*Real.log p := by
  rcases eq_or_lt_of_le h0 with h | h
  · simp [← h]
  · have : Real.log p ≤ 0 := Real.log_nonpos h0 h1
    nlinarith

/-- The binary entropy is strictly positive for `0 < p < 1`. -/
theorem shannon_two (p : ℝ) (h0 : 0 < p) (h1 : p < 1) :
    0 < -p*Real.log p - (1-p)*Real.log (1-p) := by
  have hlp : Real.log p < 0 := Real.log_neg h0 h1
  have hlq : Real.log (1-p) < 0 := Real.log_neg (by linarith) (by linarith)
  nlinarith

/-- Midpoint concavity of `log`, equivalently the AM–GM inequality. -/
theorem log_concave (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.log ((x+y)/2) ≥ (Real.log x + Real.log y)/2 := by
  have hs : Real.sqrt (x*y) ≤ (x+y)/2 := by
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ x*y), Real.sqrt_nonneg (x*y),
      sq_nonneg (Real.sqrt (x*y) - x), sq_nonneg (x - y)]
  have h1 : Real.log (Real.sqrt (x*y)) = (Real.log x + Real.log y)/2 := by
    rw [Real.log_sqrt (by positivity), Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
  rw [← h1]
  exact Real.log_le_log (by positivity) hs

end C2.IT3

