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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

/-- The set of Woodall primes: primes of the form `n * 2 ^ n - 1` with `n ≥ 1`. -/
def woodallPrimes : Set ℕ := {p | ∃ n, 0 < n ∧ p = woodall n ∧ Nat.Prime p}

@[simp] lemma woodall_def (n : ℕ) : woodall n = n * 2 ^ n - 1 := rfl

lemma woodall_two : woodall 2 = 7 := by decide
lemma woodall_three : woodall 3 = 23 := by decide
lemma woodall_six : woodall 6 = 383 := by decide

/-- `7 = W 2` is a Woodall prime. -/
lemma mem_woodallPrimes_seven : 7 ∈ woodallPrimes :=
  ⟨2, by norm_num, by simp [woodall], by norm_num⟩

/-- `23 = W 3` is a Woodall prime. -/
lemma mem_woodallPrimes_twentyThree : 23 ∈ woodallPrimes :=
  ⟨3, by norm_num, by simp [woodall], by norm_num⟩

/-- `383 = W 6` is a Woodall prime. -/
lemma mem_woodallPrimes_threeEightyThree : 383 ∈ woodallPrimes :=
  ⟨6, by norm_num, by simp [woodall], by norm_num⟩

/-- Woodall numbers are monotone in `n`. -/
lemma woodall_mono : Monotone woodall := by
  intro n m h
  have h2 : n * 2 ^ n ≤ m * 2 ^ m :=
    Nat.mul_le_mul h (Nat.pow_le_pow_right (by norm_num) h)
  simpa [woodall] using Nat.sub_le_sub_right h2 1

/-- For `n ≥ 1`, the `n`-th Woodall number is at least `n`. -/
lemma le_woodall {n : ℕ} (hn : 0 < n) : n ≤ woodall n := by
  have h1 : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 2 * n ≤ 2 ^ n * n := Nat.mul_le_mul_right n (by simpa using h1)
  have : n + 1 ≤ n * 2 ^ n := by
    have : 2 ^ n * n = n * 2 ^ n := Nat.mul_comm _ _
    omega
  simp only [woodall]
  omega

/--
**Woodall prime infinitude (conditional reduction).**

The set of Woodall primes `{p | p = n * 2 ^ n - 1 for some n ≥ 1, p prime}` is infinite
if and only if for every bound `N` there is some `n > N` with `n * 2 ^ n - 1` prime.

The infinitude of Woodall primes is an open problem, so this is a Lean-checked
equivalence (reduction), not an unconditional resolution: it shows that the set-theoretic
statement "infinitely many Woodall primes" is exactly the arithmetic statement
"Woodall primes occur for arbitrarily large indices".
-/
theorem WoodallPrimeInfinitude :
    (∀ N : ℕ, ∃ n > N, Nat.Prime (woodall n)) ↔ woodallPrimes.Infinite := by
  constructor
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hn, hp⟩ := h a
    refine ⟨woodall n, ⟨n, by omega, rfl, hp⟩, ?_⟩
    have := le_woodall (n := n) (by omega)
    omega
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt (woodall N)
    obtain ⟨n, hn, rfl, hprime⟩ := hp
    refine ⟨n, ?_, hprime⟩
    by_contra hle
    exact absurd (woodall_mono (Nat.le_of_not_lt hle)) (by omega)

end Brockian.CullenWoodall

