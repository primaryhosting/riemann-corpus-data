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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter UniqueFactorizationMonoid
open scoped Nat

namespace Brockian.BrocardProblem

/-- The `abc` conjecture, stated for natural numbers, using the radical
`UniqueFactorizationMonoid.radical` (the product of the distinct prime factors):
for every `ε > 0` there is a constant `K > 0` such that whenever `a + b = c` with
`a, b` positive and coprime, we have `c ≤ K * rad(a * b * c) ^ (1 + ε)`. -/
def ABCConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
    (c : ℝ) ≤ K * (Nat.cast (radical (a * b * c)) : ℝ) ^ (1 + ε)

/-- The set of solutions of Brocard's problem: those `n` for which `n ! + 1` is a
perfect square. Brocard's conjecture asserts that this set is exactly `{4, 5, 7}`. -/
def brocardSet : Set ℕ := {n : ℕ | ∃ m : ℕ, n ! + 1 = m ^ 2}

/-- The radical of `n !` is at most `4 ^ n`: it is a product of distinct primes `≤ n`,
hence at most the primorial of `n`, which is at most `4 ^ n`. -/
lemma radical_factorial_le (n : ℕ) : radical (n !) ≤ 4 ^ n := by
  have hrad : radical (n !) = ∏ p ∈ (n !).primeFactors, p := by
    rw [UniqueFactorizationMonoid.radical,
      UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]
    rfl
  have hsub : (n !).primeFactors ⊆ (range (n + 1)).filter Nat.Prime := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpd, -⟩ := hp
    simp only [mem_filter, mem_range]
    exact ⟨by have := hpp.dvd_factorial.1 hpd; omega, hpp⟩
  calc radical (n !) = ∏ p ∈ (n !).primeFactors, p := hrad
    _ ≤ ∏ p ∈ (range (n + 1)).filter Nat.Prime, p :=
        Finset.prod_le_prod_of_subset_of_one_le' hsub fun i hi _ => (mem_filter.1 hi).2.one_lt.le
    _ = primorial n := rfl
    _ ≤ 4 ^ n := primorial_le_4_pow n

/-- The radical occurring in the `abc` inequality for `1 + n ! = m ^ 2` is at most
`4 ^ n * m`. -/
lemma radical_brocard_le (n : ℕ) {m : ℕ} (hm : 0 < m) :
    radical (1 * n ! * m ^ 2) ≤ 4 ^ n * m := by
  have h1 : radical (1 * n ! * m ^ 2) ∣ radical (n !) * radical (m ^ 2) := by
    rw [one_mul]; exact radical_mul_dvd
  rw [radical_pow m two_ne_zero] at h1
  have h2 : radical (1 * n ! * m ^ 2) ≤ radical (n !) * radical m :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.radical_pos _) (Nat.radical_pos _)) h1
  exact h2.trans (Nat.mul_le_mul (radical_factorial_le n) (Nat.radical_le_self_iff.2 hm.ne'))

/-- Overholt's argument: assuming `abc`, every solution of Brocard's problem satisfies
`n ! ≤ C * 4096 ^ n`, with `C` depending only on the `abc` constant for `ε = 1/2`. -/
lemma factorial_le_of_abc (habc : ABCConjecture) :
    ∃ C : ℝ, 0 < C ∧ ∀ n ∈ brocardSet, (n ! : ℝ) ≤ C * 4096 ^ n := by
  obtain ⟨K, hK, h⟩ := habc (1 / 2) (by norm_num)
  refine ⟨K ^ 4, by positivity, ?_⟩
  rintro n ⟨m, hm⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have key := h 1 (n !) (m ^ 2) one_pos (Nat.factorial_pos n) (Nat.coprime_one_left _) (by omega)
  have hR : (Nat.cast (radical (1 * n ! * m ^ 2)) : ℝ) ≤ (4 : ℝ) ^ n * m := by
    have hrb := radical_brocard_le n hm0
    calc (Nat.cast (radical (1 * n ! * m ^ 2)) : ℝ) ≤ ((4 ^ n * m : ℕ) : ℝ) := by exact_mod_cast hrb
      _ = (4 : ℝ) ^ n * m := by push_cast; ring
  have hpos : (0 : ℝ) < (4 : ℝ) ^ n * m := by positivity
  have hstep : ((m : ℝ) ^ 2) ≤ K * ((4 : ℝ) ^ n * m) ^ (1 + (1 / 2 : ℝ)) := by
    have hmono := Real.rpow_le_rpow (by positivity) hR (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)
    have hcast2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
    rw [hcast2] at key
    calc ((m : ℝ) ^ 2)
        ≤ K * (Nat.cast (radical (1 * n ! * m ^ 2)) : ℝ) ^ (1 + (1 / 2 : ℝ)) := key
      _ ≤ K * ((4 : ℝ) ^ n * m) ^ (1 + (1 / 2 : ℝ)) := by nlinarith [hmono]
  have hx : ((4 : ℝ) ^ n * m) ^ (1 + (1 / 2 : ℝ)) = Real.sqrt (((4 : ℝ) ^ n * m) ^ 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((4 : ℝ) ^ n * m) 3, ← Real.rpow_mul hpos.le]
    norm_num
  rw [hx] at hstep
  have hsqrt2 : (Real.sqrt (((4 : ℝ) ^ n * m) ^ 3)) ^ 2 = ((4 : ℝ) ^ n * m) ^ 3 :=
    Real.sq_sqrt (by positivity)
  have hsq : ((m : ℝ) ^ 2) ^ 2 ≤ K ^ 2 * ((4 : ℝ) ^ n * m) ^ 3 := by
    nlinarith [hstep, Real.sqrt_nonneg (((4 : ℝ) ^ n * m) ^ 3), hsqrt2, sq_nonneg ((m : ℝ) ^ 2)]
  have e1 : ((4 : ℝ) ^ n) ^ 3 = 64 ^ n := by
    rw [← pow_mul, mul_comm n 3, pow_mul]; norm_num
  have hmle : (m : ℝ) ≤ K ^ 2 * 64 ^ n := by
    have h4 : ((4 : ℝ) ^ n * m) ^ 3 = 64 ^ n * (m : ℝ) ^ 3 := by rw [mul_pow, e1]
    rw [h4] at hsq
    have hm3 : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
    have hmul : (m : ℝ) * (m : ℝ) ^ 3 ≤ (K ^ 2 * 64 ^ n) * (m : ℝ) ^ 3 := by nlinarith [hsq]
    exact le_of_mul_le_mul_right hmul hm3
  have hcast : (n ! : ℝ) + 1 = (m : ℝ) ^ 2 := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hm
  have e2 : ((64 : ℝ) ^ n) ^ 2 = 4096 ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
  have hfin : (m : ℝ) ^ 2 ≤ K ^ 4 * 4096 ^ n := by
    have hsq2 : (m : ℝ) ^ 2 ≤ (K ^ 2 * 64 ^ n) ^ 2 := by nlinarith [hmle, hm0'.le]
    calc (m : ℝ) ^ 2 ≤ (K ^ 2 * 64 ^ n) ^ 2 := hsq2
      _ = K ^ 4 * 4096 ^ n := by rw [mul_pow, e2, ← pow_mul]
  linarith [hcast, hfin]

/-- Only finitely many `n` satisfy `n ! ≤ C * B ^ n`, since `n !` grows faster than any
geometric sequence. -/
lemma finite_of_factorial_le (C B : ℝ) (hC : 0 < C) :
    {n : ℕ | (n ! : ℝ) ≤ C * B ^ n}.Finite := by
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop |B|
  have h2 : ∀ᶠ n : ℕ in atTop, |B| ^ n / (n ! : ℝ) < 1 / C := by
    have := h.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / C by positivity))
    simpa using this
  obtain ⟨N, hN⟩ := h2.exists_forall_of_atTop
  refine (Set.finite_Iio N).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  by_contra hlt
  simp only [Set.mem_Iio, not_lt] at hlt
  have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
  have h3 := hN n hlt
  rw [div_lt_div_iff₀ hfac hC] at h3
  have habs : C * B ^ n ≤ C * |B| ^ n := by
    have hb : B ^ n ≤ |B| ^ n := (le_abs_self _).trans (by rw [abs_pow])
    nlinarith
  nlinarith

/-- The unconditional determination of all solutions of Brocard's problem with `n ≤ 7`:
they are exactly `n = 4, 5, 7` (with `m = 5, 11, 71`). -/
lemma brocard_le_seven (n : ℕ) (hn : n ≤ 7) :
    n ∈ brocardSet ↔ (n = 4 ∨ n = 5 ∨ n = 7) := by
  show (∃ m : ℕ, n ! + 1 = m ^ 2) ↔ _
  interval_cases n <;> simp [Nat.factorial] <;>
    [skip; skip; skip; skip; exact ⟨5, by norm_num⟩; exact ⟨11, by norm_num⟩; skip;
      exact ⟨71, by norm_num⟩] <;>
    (rintro m hm
     have h1 : m ≤ 27 := by nlinarith
     interval_cases m <;> omega)

/-- **Brocard's conjecture** (conditional and unconditional parts).

Brocard's problem — that `n ! + 1 = m ^ 2` has only the solutions `n = 4, 5, 7` — is open.
What is proved here is:

* (conditional, Overholt's argument) assuming the `abc` conjecture, the set of solutions is
  finite;
* (unconditional) the solutions with `n ≤ 7` are exactly `n = 4, 5, 7`. -/
theorem BrocardConjecture (habc : ABCConjecture) :
    brocardSet.Finite ∧ ∀ n ≤ 7, (n ∈ brocardSet ↔ (n = 4 ∨ n = 5 ∨ n = 7)) := by
  refine ⟨?_, brocard_le_seven⟩
  obtain ⟨C, hC, hle⟩ := factorial_le_of_abc habc
  exact (finite_of_factorial_le C 4096 hC).subset hle

end Brockian.BrocardProblem

