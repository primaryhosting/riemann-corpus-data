import Mathlib
namespace MS2.Geometry

/-- Law of cosines in an inner product space over `ℝ`. -/
theorem law_of_cosines {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    ‖a - b‖^2 = ‖a‖^2 + ‖b‖^2 - 2 * inner ℝ a b := by
  rw [norm_sub_sq_real]; ring

/-- The parallelogram law. -/
theorem parallelogram_law {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    ‖a+b‖^2 + ‖a-b‖^2 = 2*‖a‖^2 + 2*‖b‖^2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]; ring

/-- Pythagoras' theorem for orthogonal vectors. -/
theorem pythagorean_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V)
    (h : inner ℝ a b = (0:ℝ)) : ‖a+b‖^2 = ‖a‖^2 + ‖b‖^2 := by
  rw [norm_add_sq_real, h]; ring

/-- The triangle inequality. -/
theorem triangle_inequality {V : Type*} [NormedAddCommGroup V] (a b : V) :
    ‖a+b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b

/-- The Cauchy–Schwarz inequality. -/
theorem cauchy_schwarz_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a b : V) :
    |inner ℝ a b| ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b

end MS2.Geometry

