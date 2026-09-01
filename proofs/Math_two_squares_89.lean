import Mathlib

namespace Math

/-- The prime 89 is a sum of two squares: `89 = 5 ^ 2 + 8 ^ 2`. -/
theorem two_squares_89 : Nat.Prime 89 ∧ ∃ a b : ℕ, 89 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 5, 8, by norm_num⟩

end Math

