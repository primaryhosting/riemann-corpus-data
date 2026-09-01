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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Perfect Totient Infinitude
Category: Brockian Conjecture
Target: Brockian.PerfectTotient.PerfectTotientInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.PerfectTotient

/-- `totientSum n` is the sum of the iterated totients
`φ(n) + φ(φ(n)) + φ(φ(φ(n))) + ⋯` continued until the value `1` is reached
(the final `1` is included in the sum).  By convention `totientSum 0 = totientSum 1 = 0`. -/
def totientSum : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => Nat.totient (n + 2) + totientSum (Nat.totient (n + 2))
decreasing_by exact Nat.totient_lt _ (by omega)

/-- A positive natural number is a *perfect totient number* when it equals the sum of
its iterated totients. -/
def IsPerfectTotient (n : ℕ) : Prop := 0 < n ∧ totientSum n = n

theorem totientSum_eq (n : ℕ) (hn : 2 ≤ n) :
    totientSum n = Nat.totient n + totientSum (Nat.totient n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [totientSum]

/-- The iterated totient sum of `2 * 3 ^ m` is `3 ^ m`. -/
theorem totientSum_two_mul_pow_three (m : ℕ) : totientSum (2 * 3 ^ m) = 3 ^ m := by
  induction m with
  | zero => simpa using (totientSum_eq 2 le_rfl)
  | succ m ih =>
      have hcop : Nat.Coprime 2 (3 ^ (m + 1)) :=
        Nat.Coprime.pow_right (m + 1) (by norm_num)
      have hφ : Nat.totient (2 * 3 ^ (m + 1)) = 2 * 3 ^ m := by
        rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_three (by omega)]
        simp [Nat.totient_two]
      have h2 : 2 ≤ 2 * 3 ^ (m + 1) := by
        have : 1 ≤ 3 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      rw [totientSum_eq _ h2, hφ, ih]
      ring

/-- Every power `3 ^ (k + 1)` is a perfect totient number. -/
theorem isPerfectTotient_pow_three (k : ℕ) : IsPerfectTotient (3 ^ (k + 1)) := by
  refine ⟨Nat.pos_pow_of_pos _ (by norm_num), ?_⟩
  have hφ : Nat.totient (3 ^ (k + 1)) = 2 * 3 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_three (by omega)]
    simp
  have h2 : 2 ≤ 3 ^ (k + 1) := by
    calc 2 ≤ 3 ^ 1 := by norm_num
    _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [totientSum_eq _ h2, hφ, totientSum_two_mul_pow_three]
  ring

/-- **Perfect totient infinitude**: there are infinitely many perfect totient numbers. -/
theorem PerfectTotientInfinitude : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ IsPerfectTotient n := by
  intro N
  refine ⟨3 ^ (N + 1), ?_, isPerfectTotient_pow_three N⟩
  calc N < N + 1 := Nat.lt_succ_self N
  _ ≤ 3 ^ (N + 1) := Nat.le_of_lt (Nat.lt_pow_self (by norm_num))

end Brockian.PerfectTotient

