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
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.MersennePerfect

open Nat

/-- The Euclid perfect number attached to an exponent `p`: `2 ^ (p - 1) * (2 ^ p - 1)`. -/
def euclidPerfect (p : ℕ) : ℕ := 2 ^ (p - 1) * mersenne p

/-- The set of exponents `p` such that `p` and `mersenne p = 2 ^ p - 1` are both prime. -/
def mersennePrimeExponents : Set ℕ := {p : ℕ | p.Prime ∧ (mersenne p).Prime}

/-- The set of even perfect numbers. -/
def evenPerfects : Set ℕ := {n : ℕ | Even n ∧ n.Perfect}

lemma euclidPerfect_mem_evenPerfects {p : ℕ} (hp : p.Prime) (h : (mersenne p).Prime) :
    euclidPerfect p ∈ evenPerfects := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact absurd h (by decide)
    · exact hk
  have hperf : (euclidPerfect (k + 1)).Perfect := by
    simpa [euclidPerfect] using Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime k h
  refine ⟨?_, hperf⟩
  have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have : (2 : ℕ) ∣ euclidPerfect (k + 1) := by
    simpa [euclidPerfect] using h2.mul_right (mersenne (k + 1))
  exact (even_iff_two_dvd).2 this

lemma evenPerfects_subset_image :
    evenPerfects ⊆ euclidPerfect '' mersennePrimeExponents := by
  rintro n ⟨hne, hnp⟩
  obtain ⟨k, hk, rfl⟩ := Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect hne hnp
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact absurd hk (by decide)
  have hp : (k + 1).Prime := (Nat.prime_of_pow_sub_one_prime (by omega) hk).2
  exact ⟨k + 1, ⟨hp, hk⟩, by simp [euclidPerfect]⟩

lemma euclidPerfect_strictMonoOn : StrictMonoOn euclidPerfect {p : ℕ | 1 ≤ p} := by
  intro a ha b hb hab
  simp only [Set.mem_setOf_eq] at ha hb
  have h1 : (2 : ℕ) ^ (a - 1) ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℕ) ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h3 : (1 : ℕ) ≤ 2 ^ a := Nat.one_le_two_pow
  have h4 : (0 : ℕ) < 2 ^ (b - 1) := Nat.two_pow_pos _
  have h5 : mersenne a < mersenne b := by simp only [mersenne]; omega
  exact Nat.mul_lt_mul_of_le_of_lt h1 h5 h4

lemma euclidPerfect_injOn : Set.InjOn euclidPerfect mersennePrimeExponents := by
  intro a ha b hb hab
  have h : ∀ p ∈ mersennePrimeExponents, p ∈ {q : ℕ | 1 ≤ q} := by
    rintro p ⟨hp, -⟩
    exact hp.one_lt.le
  exact euclidPerfect_strictMonoOn.injOn (h a ha) (h b hb) hab

/-- **Reduction of the infinitude of Mersenne primes.**
There are infinitely many Mersenne primes (equivalently, infinitely many exponents `p` with
`p` and `2 ^ p - 1` both prime) if and only if there are infinitely many even perfect numbers.
Both statements are open; this is a Lean-checked equivalence, via Euclid–Euler. -/
theorem MersennePrimeInfinitude :
    {p : ℕ | p.Prime ∧ (mersenne p).Prime}.Infinite ↔ {n : ℕ | Even n ∧ n.Perfect}.Infinite := by
  constructor
  · intro h
    have himg : (euclidPerfect '' mersennePrimeExponents).Infinite := h.image euclidPerfect_injOn
    refine himg.mono ?_
    rintro n ⟨p, ⟨hp, hmp⟩, rfl⟩
    exact euclidPerfect_mem_evenPerfects hp hmp
  · intro h
    have himg : (euclidPerfect '' mersennePrimeExponents).Infinite :=
      Set.Infinite.mono evenPerfects_subset_image h
    exact himg.of_image _

end Brockian.MersennePerfect

