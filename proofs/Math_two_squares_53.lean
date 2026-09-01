import Mathlib

namespace Math

/-- The prime 53 is a sum of two squares: `53 = 7^2 + 2^2`. -/
theorem two_squares_53 : Nat.Prime 53 ∧ ∃ a b : ℕ, (53 : ℕ) = a ^ 2 + b ^ 2 := by
  refine ⟨by norm_num, 7, 2, by norm_num⟩

end Math

