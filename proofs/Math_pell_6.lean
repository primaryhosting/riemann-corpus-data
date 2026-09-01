import Mathlib

namespace Math

/-- The Pell equation `x² - 6·y² = 1` has a nontrivial integer solution
(i.e. one with `y ≠ 0`); explicitly `(x, y) = (5, 2)`. -/
theorem pell_6 : ∃ x y : ℤ, y ≠ 0 ∧ x ^ 2 - 6 * y ^ 2 = 1 :=
  ⟨5, 2, by norm_num, by norm_num⟩

end Math

