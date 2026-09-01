/-
# D Ocagne
Category: Fibonacci
Target: Fibonacci.dOcagne
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

/-- Auxiliary form of d'Ocagne's identity, with `m` written as `n + k`. -/
theorem dOcagne_aux (n k : ℕ) :
    (Nat.fib (n + k) : ℤ) * Nat.fib (n + 1) - Nat.fib (n + k + 1) * Nat.fib n
      = (-1) ^ n * Nat.fib k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : Nat.fib (n + 1 + 1) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have h2 : Nat.fib (n + 1 + k + 1) = Nat.fib (n + k) + Nat.fib (n + 1 + k) := by
        have : n + 1 + k = n + k + 1 := by omega
        rw [this]
        exact Nat.fib_add_two
      rw [h2, h1, pow_succ]
      have e1 : n + 1 + k = n + k + 1 := by omega
      rw [e1]
      push_cast
      nlinarith [ih]

/-- **d'Ocagne's identity** :
`fib m * fib (n+1) - fib (m+1) * fib n = (-1)^n * fib (m - n)` for `n ≤ m`. -/
theorem dOcagne {m n : ℕ} (h : n ≤ m) :
    (Nat.fib m : ℤ) * Nat.fib (n + 1) - Nat.fib (m + 1) * Nat.fib n
      = (-1) ^ n * Nat.fib (m - n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using dOcagne_aux n k

/-- Addition form avoiding subtraction:
`fib (m + n + 1) = fib (m+1) * fib (n+1) + fib m * fib n`. -/
theorem dOcagne_addition_form (m n : ℕ) :
    (Nat.fib (m + n + 1) : ℤ) = Nat.fib (m + 1) * Nat.fib (n + 1) + Nat.fib m * Nat.fib n := by
  have := Nat.fib_add m n
  push_cast [this]
  ring

end Fibonacci


