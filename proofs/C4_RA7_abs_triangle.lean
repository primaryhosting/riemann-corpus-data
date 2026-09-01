import Mathlib
namespace C4.RA7

/-- Triangle inequality for the absolute value on `ℝ` (Mathlib: `abs_add_le`). -/
theorem abs_triangle (a b : ℝ) : |a + b| ≤ |a| + |b| := abs_add_le a b

/-- Squares of reals are nonnegative (Mathlib: `sq_nonneg`). -/
theorem sq_nonneg_real (a : ℝ) : 0 ≤ a^2 := sq_nonneg a

/-- AM–GM for two nonnegative reals: `2√(ab) ≤ a + b`. -/
theorem amgm2_real (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 2 * Real.sqrt (a*b) ≤ a + b := by
  rw [Real.sqrt_mul ha]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

end C4.RA7

