import Mathlib

namespace Math

/-- Cassini's identity at n = 12: `F(11) * F(13) - F(12)^2 = (-1)^12`. -/
theorem cassini_12 :
    (Nat.fib 11 : ℤ) * (Nat.fib 13 : ℤ) - (Nat.fib 12 : ℤ) ^ 2 = (-1) ^ 12 := by
  norm_num [Nat.fib]

end Math

