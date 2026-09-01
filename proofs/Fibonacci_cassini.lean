import Mathlib

/-!
# Cassini
Category: Fibonacci
Target: Fibonacci.cassini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Fibonacci

/-- **Cassini's identity**, stated over `ℤ` to avoid truncated subtraction:
for every `n : ℕ`, `F (n+2) * F n - F (n+1) ^ 2 = (-1) ^ (n+1)`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n) - (Nat.fib (n + 1)) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h3 : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    rw [h3] at *
    rw [h2] at ih ⊢
    have hp : ((-1 : ℤ)) ^ (k + 1 + 1) = -(-1) ^ (k + 1) := by ring
    push_cast at ih ⊢
    rw [hp]
    linear_combination -ih

end Fibonacci

