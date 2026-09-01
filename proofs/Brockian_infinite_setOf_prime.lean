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

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is proved here

Andrica's conjecture (`√p_{n+1} - √p_n < 1` for all `n`) is an open problem, and Mathlib
contains no statement of it (a search of the library turns up no lemma about differences of
square roots of consecutive primes). What is proved here is a Lean-checked *conditional
reduction*:

* `AndricaConjecture : Oppermann → AndricaStatement`,

together with the unconditional ingredients

* `sqrt_sub_sqrt_lt_one` : a prime gap bound `q ≤ p + 2 * Nat.sqrt p + 1` implies `√q - √p < 1`;
* `exists_prime_gap_of_oppermann` : Oppermann's conjecture gives exactly such a gap bound;
* `andricaStatement_iff` : the equivalent formulation `p_{n+1} < (√p_n + 1)^2`;
* `andrica_zero` : the base case `√3 - √2 < 1`.

Mathlib API used: `Nat.nth`, `Nat.nth_count`, `Nat.nth_lt_nth`, `Nat.nth_le_nth`,
`Nat.lt_nth_iff_count_lt`, `Nat.infinite_setOf_prime`, `Nat.sqrt_le`, `Nat.lt_succ_sqrt`,
`Real.sqrt_lt_sqrt`, `Real.sq_sqrt`, `Real.sqrt_sq`.
-/

namespace Brockian
namespace AndricaConjecture

open Nat

/-- The `n`-th prime, `nthPrime 0 = 2`. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

lemma infinite_setOf_prime : {p | Nat.Prime p}.Infinite := Nat.infinite_setOf_prime

lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite infinite_setOf_prime n

lemma nthPrime_lt_nthPrime_succ (n : ℕ) : nthPrime n < nthPrime (n + 1) :=
  (Nat.nth_lt_nth infinite_setOf_prime).2 (Nat.lt_succ_self n)

/-- `nthPrime (n+1)` is the *least* prime exceeding `nthPrime n`. -/
lemma nthPrime_succ_le_of_prime_of_lt {n r : ℕ} (hr : Nat.Prime r) (h : nthPrime n < r) :
    nthPrime (n + 1) ≤ r := by
  classical
  have hcount : n < Nat.count Nat.Prime r :=
    (Nat.lt_nth_iff_count_lt infinite_setOf_prime).2 h
  have h1 : nthPrime (n + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime r) :=
    (Nat.nth_le_nth infinite_setOf_prime).2 hcount
  rwa [Nat.nth_count hr] at h1

/-- Oppermann's conjecture: for every `m ≥ 2` there is a prime strictly between
`m^2 - m` and `m^2`, and a prime strictly between `m^2` and `m^2 + m`. -/
def Oppermann : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    (∃ p : ℕ, Nat.Prime p ∧ m ^ 2 - m < p ∧ p < m ^ 2) ∧
    (∃ p : ℕ, Nat.Prime p ∧ m ^ 2 < p ∧ p < m ^ 2 + m)

/-- Andrica's conjecture: `√p_{n+1} - √p_n < 1` for all `n`. -/
def AndricaStatement : Prop :=
  ∀ n : ℕ, Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1

/-- A prime is never a perfect square, so `Nat.sqrt p ^ 2 < p`. -/
lemma sq_sqrt_lt_of_prime {p : ℕ} (hp : Nat.Prime p) : Nat.sqrt p ^ 2 < p := by
  rcases lt_or_eq_of_le (Nat.sqrt_le p) with h | h
  · simpa [pow_two] using h
  · exfalso
    have h2 := hp.two_le
    rcases Nat.Prime.eq_one_or_self_of_dvd hp _ ⟨Nat.sqrt p, h.symm⟩ with h1 | h1 <;>
      rw [h1] at h <;> nlinarith

/-- Key unconditional reduction: if `q ≤ p + 2 * Nat.sqrt p + 1` for a prime `p` and a
natural number `q`, then `√q - √p < 1`. -/
lemma sqrt_sub_sqrt_lt_one {p q : ℕ} (hp : Nat.Prime p) (hq : q ≤ p + 2 * Nat.sqrt p + 1) :
    Real.sqrt q - Real.sqrt p < 1 := by
  set m : ℕ := Nat.sqrt p with hm
  have hmp : (m : ℝ) < Real.sqrt p := by
    have h1 : ((m : ℝ)) ^ 2 < (p : ℝ) := by exact_mod_cast sq_sqrt_lt_of_prime hp
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (p:ℝ)),
      Real.sqrt_nonneg (p : ℝ)]
  have hqlt : (q : ℝ) < (Real.sqrt p + 1) ^ 2 := by
    have h1 : (q : ℝ) ≤ (p : ℝ) + 2 * (m : ℝ) + 1 := by exact_mod_cast hq
    have h2 : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith
  have h3 : Real.sqrt q < Real.sqrt p + 1 := by
    have hnn : (0 : ℝ) ≤ Real.sqrt p + 1 := by positivity
    have := Real.sqrt_lt_sqrt (by positivity) hqlt
    rwa [Real.sqrt_sq hnn] at this
  linarith

/-- Under Oppermann's conjecture, the gap after any prime `p` is at most `2 * Nat.sqrt p + 1`:
there is a prime `r` with `p < r ≤ p + 2 * Nat.sqrt p + 1`. -/
lemma exists_prime_gap_of_oppermann (h : Oppermann) {p : ℕ} (hp : Nat.Prime p) :
    ∃ r : ℕ, Nat.Prime r ∧ p < r ∧ r ≤ p + 2 * Nat.sqrt p + 1 := by
  set m : ℕ := Nat.sqrt p with hm
  have hlow : m ^ 2 < p := sq_sqrt_lt_of_prime hp
  have hhigh : p < (m + 1) ^ 2 := by
    have h4 := Nat.lt_succ_sqrt p
    calc p < (m + 1) * (m + 1) := h4
      _ = (m + 1) ^ 2 := by ring
  have hm1 : 1 ≤ m := by
    have := hp.two_le
    exact Nat.le_sqrt.2 (by omega)
  obtain ⟨⟨a, ha, ha1, ha2⟩, ⟨b, hb, hb1, hb2⟩⟩ := h (m + 1) (by omega)
  by_cases hcase : p < m ^ 2 + m
  · -- use the prime `a` in `((m+1)^2 - (m+1), (m+1)^2)`
    refine ⟨a, ha, ?_, ?_⟩
    · have : (m + 1) ^ 2 - (m + 1) = m ^ 2 + m := by
        have : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
        omega
      omega
    · have h2 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
      omega
  · -- use the prime `b` in `((m+1)^2, (m+1)^2 + (m+1))`
    refine ⟨b, hb, ?_, ?_⟩
    · have h2 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
      omega
    · have h2 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
      omega

/-- **Andrica's conjecture, conditional on Oppermann's conjecture.**
Andrica's conjecture (`√p_{n+1} - √p_n < 1`) is a well-known open problem; here we give a
Lean-checked reduction: it follows from Oppermann's conjecture. -/
theorem AndricaConjecture (h : Oppermann) : AndricaStatement := by
  intro n
  obtain ⟨r, hr, hr1, hr2⟩ := exists_prime_gap_of_oppermann h (nthPrime_prime n)
  have hle : nthPrime (n + 1) ≤ nthPrime n + 2 * Nat.sqrt (nthPrime n) + 1 :=
    le_trans (nthPrime_succ_le_of_prime_of_lt hr hr1) hr2
  exact sqrt_sub_sqrt_lt_one (nthPrime_prime n) hle

/-- Reformulation of Andrica's conjecture: `p_{n+1} < (√p_n + 1)^2`. -/
lemma andricaStatement_iff :
    AndricaStatement ↔ ∀ n : ℕ, (nthPrime (n + 1) : ℝ) < (Real.sqrt (nthPrime n) + 1) ^ 2 := by
  constructor
  · intro h n
    have h1 : Real.sqrt (nthPrime (n + 1)) < Real.sqrt (nthPrime n) + 1 := by
      have := h n; linarith
    have h2 : (0 : ℝ) ≤ Real.sqrt (nthPrime n) + 1 := by positivity
    have h3 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (nthPrime (n + 1) : ℝ))
    nlinarith [Real.sqrt_nonneg ((nthPrime (n + 1) : ℝ))]
  · intro h n
    have h2 : (0 : ℝ) ≤ Real.sqrt (nthPrime n) + 1 := by positivity
    have := Real.sqrt_lt_sqrt (by positivity) (h n)
    rw [Real.sqrt_sq h2] at this
    linarith

@[simp] lemma nthPrime_zero : nthPrime 0 = 2 := by
  have := Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num)
  simp [nthPrime] at this ⊢

@[simp] lemma nthPrime_one : nthPrime 1 = 3 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
  have hc : Nat.count Nat.Prime 3 = 1 := by decide
  rw [hc] at h
  exact h

/-- Sanity check that the hypothesis `Oppermann` is not vacuous at small values: the two
required primes exist for `m = 2` and `m = 3`. -/
lemma oppermann_two_three :
    ((∃ p : ℕ, Nat.Prime p ∧ 2 ^ 2 - 2 < p ∧ p < 2 ^ 2) ∧
      (∃ p : ℕ, Nat.Prime p ∧ 2 ^ 2 < p ∧ p < 2 ^ 2 + 2)) ∧
    ((∃ p : ℕ, Nat.Prime p ∧ 3 ^ 2 - 3 < p ∧ p < 3 ^ 2) ∧
      (∃ p : ℕ, Nat.Prime p ∧ 3 ^ 2 < p ∧ p < 3 ^ 2 + 3)) :=
  ⟨⟨⟨3, by norm_num⟩, ⟨5, by norm_num⟩⟩, ⟨⟨7, by norm_num⟩, ⟨11, by norm_num⟩⟩⟩

/-- Unconditional base case: Andrica's inequality holds for the first pair of primes. -/
lemma andrica_zero : Real.sqrt (nthPrime 1) - Real.sqrt (nthPrime 0) < 1 := by
  have h := sqrt_sub_sqrt_lt_one (p := 2) (q := 3) (by norm_num) (by norm_num)
  simpa using h

end AndricaConjecture
end Brockian

#print axioms Brockian.AndricaConjecture.AndricaConjecture

