import Mathlib
namespace C4.Geo3

/-- The inner product of a vector with itself is nonnegative. -/
theorem inner_self_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a : V) :
    0 ≤ (inner ℝ a a : ℝ) :=
  real_inner_self_nonneg

/-- Scaling a vector by a real number scales its norm by the absolute value. -/
theorem norm_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ) (a : V) :
    ‖c • a‖ = |c| * ‖a‖ := by
  rw [_root_.norm_smul, Real.norm_eq_abs]

/-- The Cauchy–Schwarz inequality in a real inner product space. -/
theorem cauchy_schwarz_geo {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    (inner ℝ a b : ℝ)^2 ≤ (inner ℝ a a : ℝ) * (inner ℝ b b : ℝ) := by
  rw [sq]
  exact real_inner_mul_inner_self_le a b

end C4.Geo3

