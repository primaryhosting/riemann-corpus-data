import Mathlib

namespace Math

/-- The prime 13 is a sum of two squares. -/
theorem two_squares_13 : Nat.Prime 13 ∧ ∃ a b : ℕ, 13 = a ^ 2 + b ^ 2 := by
  refine ⟨by norm_num, 2, 3, by norm_num⟩

end Math

