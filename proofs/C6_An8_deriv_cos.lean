import Mathlib
namespace C6.An8

/-- The derivative of `cos` is `-sin`. -/
theorem deriv_cos (x : ℝ) : deriv Real.cos x = -Real.sin x := Real.deriv_cos

/-- The Pythagorean identity `sin² x + cos² x = 1`. -/
theorem sin_sq_add_cos_sq (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq x

/-- The real exponential is never zero. -/
theorem exp_ne_zero (x : ℝ) : Real.exp x ≠ 0 := Real.exp_ne_zero x

end C6.An8

