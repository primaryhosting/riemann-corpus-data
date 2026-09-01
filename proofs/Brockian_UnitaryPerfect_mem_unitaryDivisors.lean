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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to appear before any other syntax,
so the mandated header block is placed immediately after the single `import Mathlib` line.
-/

open Finset

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd d (n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ := n.divisors.filter fun d => Nat.Coprime d (n / d)

/-- `usigma n = σ*(n)` is the sum of the unitary divisors of `n`. -/
def usigma (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is *unitary perfect* if it is positive and the sum of its unitary divisors is `2 * n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ usigma n = 2 * n

lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

/-! ## Multiplicativity of `usigma` -/

/-- `σ*` is multiplicative: on coprime arguments it splits as a product. -/
theorem usigma_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  rw [usigma, usigma, usigma, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun d => (Nat.gcd d m, Nat.gcd d n)) (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨hdvd, -, hcop⟩ := hd
    have hab : Nat.gcd d m * Nat.gcd d n = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hdvd
    set a := Nat.gcd d m with ha
    set b := Nat.gcd d n with hb
    have ham : a ∣ m := Nat.gcd_dvd_right d m
    have hbn : b ∣ n := Nat.gcd_dvd_right d n
    have hdiv : (m * n) / d = (m / a) * (n / b) := by
      rw [← hab, Nat.div_mul_div_comm ham hbn]
    rw [hdiv, ← hab] at hcop
    have h1 : Nat.Coprime a (m / a) :=
      (hcop.coprime_dvd_left ⟨b, rfl⟩).coprime_dvd_right ⟨n / b, rfl⟩
    have h2 : Nat.Coprime b (n / b) :=
      (hcop.coprime_dvd_left ⟨a, mul_comm a b⟩).coprime_dvd_right ⟨m / a, mul_comm _ _⟩
    simp only [Finset.mem_product, mem_unitaryDivisors]
    exact ⟨⟨ham, hm, h1⟩, ⟨hbn, hn, h2⟩⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ham, -, ha⟩, ⟨hbn, -, hb⟩⟩ := hab
    rw [mem_unitaryDivisors]
    refine ⟨mul_dvd_mul ham hbn, mul_ne_zero hm hn, ?_⟩
    rw [← Nat.div_mul_div_comm ham hbn]
    have hamn : Nat.Coprime a (n / b) :=
      (h.coprime_dvd_left ham).coprime_dvd_right (Nat.div_dvd_of_dvd hbn)
    have hbmn : Nat.Coprime b (m / a) :=
      (h.symm.coprime_dvd_left hbn).coprime_dvd_right (Nat.div_dvd_of_dvd ham)
    exact Nat.Coprime.mul_left (ha.mul_right hamn) (hbmn.mul_right hb)
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hd.1
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ham, -, ha⟩, ⟨hbn, -, hb⟩⟩ := hab
    have h1 : Nat.gcd (a * b) m = a := by
      rw [mul_comm]
      exact Nat.gcd_mul_of_coprime_of_dvd (h.symm.coprime_dvd_left hbn) ham
    have h2 : Nat.gcd (a * b) n = b :=
      Nat.gcd_mul_of_coprime_of_dvd (h.coprime_dvd_left ham) hbn
    simp [h1, h2]
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hd.1).symm

/-- The only unitary divisors of a prime power `p ^ k` are `1` and `p ^ k`. -/
theorem unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  have hp1 : 1 < p := hp.one_lt
  ext d
  rw [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hdvd, -, hcop⟩
    obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rw [Nat.pow_div hik hp.pos] at hcop
    rcases Nat.eq_zero_or_pos i with hi | hi
    · left; simp [hi]
    · right
      have hki : k - i = 0 := by
        by_contra hne
        have hd1 : p ∣ p ^ i := dvd_pow_self p (by omega)
        have hd2 : p ∣ p ^ (k - i) := dvd_pow_self p hne
        have hone : p ∣ 1 := hcop ▸ Nat.dvd_gcd hd1 hd2
        have := Nat.le_of_dvd one_pos hone
        omega
      have hik' : i = k := by omega
      rw [hik']
  · rintro (rfl | rfl)
    · exact ⟨one_dvd _, by positivity, by simp⟩
    · refine ⟨dvd_rfl, by positivity, ?_⟩
      simp [Nat.div_self (by positivity : 0 < p ^ k)]

/-- `σ*(p ^ k) = p ^ k + 1` for a prime power with positive exponent. -/
theorem usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : usigma (p ^ k) = p ^ k + 1 := by
  have h1 : (1 : ℕ) ≠ p ^ k := by
    have := Nat.one_lt_pow hk hp.one_lt
    omega
  rw [usigma, unitaryDivisors_prime_pow hp, Finset.sum_insert (by simpa using h1),
    Finset.sum_singleton]
  omega

/-- One step of the evaluation of `σ*` on an explicit factorization. -/
theorem usigma_step {m p k : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hk : k ≠ 0)
    (h : Nat.Coprime m (p ^ k)) : usigma (m * p ^ k) = usigma m * (p ^ k + 1) := by
  rw [usigma_mul hm (pow_ne_zero _ hp.pos.ne') h, usigma_prime_pow hp hk]

/-! ## The five classically known unitary perfect numbers -/

theorem usigma_six : usigma 6 = 12 := by
  rw [show (6 : ℕ) = 2 ^ 1 * 3 ^ 1 by norm_num]
  rw [usigma_step (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    usigma_prime_pow (by norm_num) (by norm_num)]
  norm_num

theorem usigma_sixty : usigma 60 = 120 := by
  rw [show (60 : ℕ) = 2 ^ 2 * 3 ^ 1 * 5 ^ 1 by norm_num]
  repeat rw [usigma_step (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [usigma_prime_pow (by norm_num) (by norm_num)]
  norm_num

theorem usigma_ninety : usigma 90 = 180 := by
  rw [show (90 : ℕ) = 2 ^ 1 * 3 ^ 2 * 5 ^ 1 by norm_num]
  repeat rw [usigma_step (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [usigma_prime_pow (by norm_num) (by norm_num)]
  norm_num

theorem usigma_87360 : usigma 87360 = 174720 := by
  rw [show (87360 : ℕ) = 2 ^ 6 * 3 ^ 1 * 5 ^ 1 * 7 ^ 1 * 13 ^ 1 by norm_num]
  repeat rw [usigma_step (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [usigma_prime_pow (by norm_num) (by norm_num)]
  norm_num

theorem usigma_fifth : usigma 146361946186458562560000 = 292723892372917125120000 := by
  rw [show (146361946186458562560000 : ℕ) =
      2 ^ 18 * 3 ^ 1 * 5 ^ 4 * 7 ^ 1 * 11 ^ 1 * 13 ^ 1 * 19 ^ 1 * 37 ^ 1 * 79 ^ 1 * 109 ^ 1 *
        157 ^ 1 * 313 ^ 1 by norm_num]
  repeat rw [usigma_step (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [usigma_prime_pow (by norm_num) (by norm_num)]
  norm_num

/-- The five classically known unitary perfect numbers. -/
def knownUnitaryPerfect : Finset ℕ := {6, 60, 90, 87360, 146361946186458562560000}

theorem card_knownUnitaryPerfect : knownUnitaryPerfect.card = 5 := by
  decide

theorem unitaryPerfect_of_mem_known {n : ℕ} (hn : n ∈ knownUnitaryPerfect) : IsUnitaryPerfect n := by
  fin_cases hn
  · exact ⟨by norm_num, by rw [usigma_six]⟩
  · exact ⟨by norm_num, by rw [usigma_sixty]⟩
  · exact ⟨by norm_num, by rw [usigma_ninety]⟩
  · exact ⟨by norm_num, by rw [usigma_87360]⟩
  · exact ⟨by norm_num, by rw [usigma_fifth]⟩

/-- Unconditionally, there are at least five unitary perfect numbers. -/
theorem fiveUnitaryPerfectExist :
    ∃ S : Finset ℕ, S.card = 5 ∧ ∀ n ∈ S, IsUnitaryPerfect n :=
  ⟨knownUnitaryPerfect, card_knownUnitaryPerfect, fun _ hn => unitaryPerfect_of_mem_known hn⟩

/-! ## The sixth unitary perfect number

Whether a sixth unitary perfect number exists is a well-known open problem, so the statement
below is a *conditional reduction*: the existence of six unitary perfect numbers is proved
from (and in fact is equivalent to) the existence of a single unitary perfect number outside
the classically known list of five. -/

/-- **Conditional reduction.** If some unitary perfect number lies outside the classically known
list of five, then there are six unitary perfect numbers, i.e. a sixth unitary perfect number
exists. (Unconditional existence of a sixth unitary perfect number is an open problem.) -/
theorem SixthUnitaryPerfectExists
    (h : ∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect) :
    ∃ S : Finset ℕ, S.card = 6 ∧ ∀ n ∈ S, IsUnitaryPerfect n := by
  obtain ⟨n, hn, hnot⟩ := h
  refine ⟨insert n knownUnitaryPerfect, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hnot, card_knownUnitaryPerfect]
  · intro m hm
    rcases Finset.mem_insert.1 hm with rfl | hm
    · exact hn
    · exact unitaryPerfect_of_mem_known hm

/-- The reduction is sharp: six unitary perfect numbers exist **iff** some unitary perfect number
is not one of the five classically known ones. -/
theorem sixthUnitaryPerfectExists_iff :
    (∃ S : Finset ℕ, S.card = 6 ∧ ∀ n ∈ S, IsUnitaryPerfect n) ↔
      ∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect := by
  refine ⟨?_, SixthUnitaryPerfectExists⟩
  rintro ⟨S, hcard, hS⟩
  by_contra hcon
  push_neg at hcon
  have hsub : S ⊆ knownUnitaryPerfect := fun n hn => hcon n (hS n hn)
  have := Finset.card_le_card hsub
  rw [hcard, card_knownUnitaryPerfect] at this
  omega

end Brockian.UnitaryPerfect

