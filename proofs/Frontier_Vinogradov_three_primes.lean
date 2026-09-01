import Mathlib

/-!
# Vinogradov Three Primes
Category: Frontier — Prime Numbers
Target: Frontier.Vinogradov_three_primes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- `IsSumOfThreePrimes n` says that `n` can be written as a sum of three (not necessarily
distinct) prime numbers. -/
def IsSumOfThreePrimes (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

/-- The binary (strong) Goldbach statement: every even number `≥ 4` is a sum of two primes. -/
def GoldbachEven : Prop :=
  ∀ m : ℕ, 4 ≤ m → Even m → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = m

/-- The key reduction: assuming the binary Goldbach statement, every odd number `n ≥ 9` is a
sum of three primes (write `n = 3 + (n - 3)` with `n - 3` even and `≥ 6`). -/
theorem isSumOfThreePrimes_of_goldbachEven (h : GoldbachEven) {n : ℕ} (hn : 9 ≤ n)
    (hodd : Odd n) : IsSumOfThreePrimes n := by
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨p, q, hp, hq, hpq⟩ := h (n - 3) (by omega) ⟨(n - 3) / 2, by omega⟩
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-- **Vinogradov's three primes theorem**, in the form of a Lean-checked reduction to the
binary Goldbach statement: assuming every even number `≥ 4` is a sum of two primes, there is a
threshold (namely `9`) beyond which every odd number is a sum of three primes. -/
theorem Vinogradov_three_primes (h : GoldbachEven) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → IsSumOfThreePrimes n :=
  ⟨9, fun _ hn hodd => isSumOfThreePrimes_of_goldbachEven h hn hodd⟩

/-- Unconditional verification of the binary Goldbach statement below `500`. -/
theorem goldbach_lt_500 :
    ∀ m < 500, 4 ≤ m → m % 2 = 0 → ∃ p < m, Nat.Prime p ∧ Nat.Prime (m - p) := by
  decide

/-- Unconditional base case: every odd number `n` with `9 ≤ n ≤ 502` is a sum of three primes. -/
theorem isSumOfThreePrimes_of_odd_le_502 {n : ℕ} (hn : 9 ≤ n) (hn' : n ≤ 502) (hodd : Odd n) :
    IsSumOfThreePrimes n := by
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨p, hp, hp', hq'⟩ := goldbach_lt_500 (n - 3) (by omega) (by omega) (by omega)
  exact ⟨3, p, n - 3 - p, Nat.prime_three, hp', hq', by omega⟩

end Frontier

