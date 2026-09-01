import Mathlib

namespace Math

/-- The prime 113 is a sum of two squares: `113 = 7^2 + 8^2`. -/
theorem two_squares_113 : Nat.Prime 113 ∧ ∃ a b : ℕ, 113 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 7, 8, by norm_num⟩

end Math

