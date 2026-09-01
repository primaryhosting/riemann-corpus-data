import Mathlib

def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- For `n > 0`, `n ^ 2 + 1` lies strictly between the consecutive squares
`n ^ 2` and `(n + 1) ^ 2`, hence is never a perfect square. -/
theorem not_isSquare_sq_add_one (n : ℕ) (hn : 0 < n) : ¬ IsSquare (n ^ 2 + 1) := by
  rintro ⟨r, hr⟩
  have h1 : n < r := by nlinarith
  have h2 : r < n + 1 := by nlinarith
  omega

