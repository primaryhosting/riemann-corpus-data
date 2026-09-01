/-
# Cassini 2
Category: Pure Mathematics
Target: Math.cassini_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- NOTE: the header above is written as a plain block comment `/- ... -/` rather than a
-- module docstring `/-! ... -/`, because Lean 4 does not allow a module docstring to
-- appear before the `import` commands. The text is otherwise verbatim.

import Mathlib

namespace Math

/-- Cassini's identity at `n = 2`: `F(1) * F(3) - F(2) ^ 2 = (-1) ^ 2`,
where `F` is the Fibonacci sequence (`Nat.fib`). -/
theorem cassini_2 :
    (Nat.fib 1 : ℤ) * (Nat.fib 3 : ℤ) - (Nat.fib 2 : ℤ) ^ 2 = (-1) ^ 2 := by
  norm_num [Nat.fib]

end Math

