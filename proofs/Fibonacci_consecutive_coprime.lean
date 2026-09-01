/-
# Consecutive Coprime
Category: Fibonacci
Target: Fibonacci.consecutive_coprime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Fibonacci

/-- Consecutive Fibonacci numbers are coprime. -/
theorem consecutive_coprime (n : ℕ) : Nat.Coprime (Nat.fib n) (Nat.fib (n + 1)) :=
  Nat.fib_coprime_fib_succ n

end Fibonacci

