import Mathlib

/-!
# Zeckendorf Small
Category: Fibonacci
Target: Fibonacci.zeckendorf_small
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

/-- Zeckendorf representation of 100: `100 = 89 + 8 + 3 = fib 11 + fib 6 + fib 4`,
a sum of Fibonacci numbers whose indices (11, 6, 4) are pairwise non-consecutive. -/
theorem zeckendorf_small : 100 = Nat.fib 11 + Nat.fib 6 + Nat.fib 4 := by
  decide

end Fibonacci

