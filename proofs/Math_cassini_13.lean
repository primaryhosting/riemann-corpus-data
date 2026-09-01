import Mathlib

namespace Math

/-- Cassini's identity at n = 13: `F(12) * F(14) - F(13)^2 = (-1)^13`. -/
theorem cassini_13 :
    (Nat.fib 12 : ℤ) * (Nat.fib 14 : ℤ) - (Nat.fib 13 : ℤ) ^ 2 = (-1) ^ 13 := by
  norm_num [Nat.fib]

end Math

