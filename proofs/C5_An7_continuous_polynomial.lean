import Mathlib
namespace C5.An7
theorem continuous_polynomial (a b c : ℝ) : Continuous (fun x : ℝ => a*x^2 + b*x + c) := by
  fun_prop
theorem deriv_sin (x : ℝ) : deriv Real.sin x = Real.cos x := Real.deriv_sin ▸ rfl
theorem abs_le_of_sq_le (a b : ℝ) (h : a^2 ≤ b^2) (hb : 0 ≤ b) : -b ≤ a ∧ a ≤ b := by
  constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
end C5.An7

