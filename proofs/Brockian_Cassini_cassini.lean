import Mathlib
namespace Brockian.Cassini
/-- Cassini's identity for Fibonacci numbers: F_n·F_{n+2} − F_{n+1}² = (−1)^{n+1}. -/
theorem cassini (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2)) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      rw [Nat.fib_add_two]
    have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := by
      rw [Nat.fib_add_two]
    push_cast [h1, h2] at *
    ring_nf at ih ⊢
    linarith [ih]
end Brockian.Cassini

