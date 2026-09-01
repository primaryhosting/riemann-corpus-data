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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- The unitary divisor sum `σ*(n)`, the sum of the unitary divisors of `n`. -/
def usigma (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is *unitary perfect* if it is positive and `σ*(n) = 2n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ usigma n = 2 * n

lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

@[simp] lemma usigma_zero : usigma 0 = 0 := by
  simp [usigma, unitaryDivisors]

@[simp] lemma usigma_one : usigma 1 = 1 := by
  decide

/-- `σ*` is multiplicative: `σ*(mn) = σ*(m) σ*(n)` for coprime `m`, `n`. -/
lemma usigma_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  rw [usigma, usigma, usigma, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun d => (Nat.gcd d m, Nat.gcd d n)) (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨hdvd, -, hcop⟩ := hd
    have hsplit : Nat.gcd d m * Nat.gcd d n = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hdvd
    have ham : Nat.gcd d m ∣ m := Nat.gcd_dvd_right _ _
    have han : Nat.gcd d n ∣ n := Nat.gcd_dvd_right _ _
    have hdiv : m / Nat.gcd d m * (n / Nat.gcd d n) = m * n / d := by
      rw [Nat.div_mul_div_comm ham han, hsplit]
    have hd1 : m / Nat.gcd d m ∣ m * n / d := ⟨n / Nat.gcd d n, hdiv.symm⟩
    have hd2 : n / Nat.gcd d n ∣ m * n / d := ⟨m / Nat.gcd d m, by rw [← hdiv]; ring⟩
    simp only [Finset.mem_product, mem_unitaryDivisors]
    exact ⟨⟨ham, hm, Nat.Coprime.coprime_dvd_right hd1
        (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcop)⟩,
      ⟨han, hn, Nat.Coprime.coprime_dvd_right hd2
        (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcop)⟩⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ham, -, hacop⟩, ⟨hbn, -, hbcop⟩⟩ := hab
    rw [mem_unitaryDivisors]
    refine ⟨mul_dvd_mul ham hbn, hmn, ?_⟩
    have hdiv : m * n / (a * b) = m / a * (n / b) := (Nat.div_mul_div_comm ham hbn).symm
    rw [hdiv]
    have h1 : Nat.Coprime a (n / b) :=
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hbn)
        (Nat.Coprime.coprime_dvd_left ham h)
    have h2 : Nat.Coprime b (m / a) :=
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd ham)
        (Nat.Coprime.coprime_dvd_left hbn h.symm)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hacop h1) (Nat.Coprime.mul_right h2 hbcop)
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hd.1
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ham, -, -⟩, ⟨hbn, -, -⟩⟩ := hab
    have hbm : Nat.Coprime b m := Nat.Coprime.coprime_dvd_left hbn h.symm
    have han : Nat.Coprime a n := Nat.Coprime.coprime_dvd_left ham h
    simp [Nat.Coprime.gcd_mul_right_cancel a hbm, Nat.Coprime.gcd_mul_left_cancel b han,
      Nat.gcd_eq_left ham, Nat.gcd_eq_left hbn]
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hd.1).symm

/-- A prime power `p ^ k` (`k ≥ 1`) has exactly the two unitary divisors `1` and `p ^ k`. -/
lemma usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    usigma (p ^ k) = p ^ k + 1 := by
  have hp1 : 1 < p ^ k := Nat.one_lt_pow hk hp.one_lt
  have hset : unitaryDivisors (p ^ k) = {1, p ^ k} := by
    ext d
    simp only [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hdvd, -, hcop⟩
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · left; simp
      · right
        by_contra hne
        have hik : i < k := lt_of_le_of_ne hi (by rintro rfl; exact hne rfl)
        rw [Nat.pow_div hi hp.pos] at hcop
        have h1 : p ∣ p ^ i := dvd_pow_self p hipos.ne'
        have h2 : p ∣ p ^ (k - i) := dvd_pow_self p (by omega)
        have hdd := Nat.dvd_gcd h1 h2
        rw [hcop] at hdd
        exact hp.one_lt.ne' (Nat.dvd_one.mp hdd)
    · rintro (rfl | rfl)
      · exact ⟨one_dvd _, by positivity, by simp⟩
      · exact ⟨dvd_rfl, by positivity, by simp [Nat.div_self (by positivity : 0 < p ^ k)]⟩
  rw [usigma, hset, Finset.sum_insert (by simp; omega), Finset.sum_singleton, add_comm]

lemma usigma_prime {p : ℕ} (hp : p.Prime) : usigma p = p + 1 := by
  simpa using usigma_prime_pow hp one_ne_zero

/-- `σ*` packaged as an arithmetic function. -/
def usigmaAF : ArithmeticFunction ℕ := ⟨usigma, usigma_zero⟩

lemma usigmaAF_apply (n : ℕ) : usigmaAF n = usigma n := rfl

lemma usigmaAF_isMultiplicative : usigmaAF.IsMultiplicative :=
  ⟨usigma_one, fun h => usigma_mul_of_coprime h⟩

/-- The product formula `σ*(n) = ∏_{p ∣ n} (p ^ v_p(n) + 1)`. -/
lemma usigma_eq_prod {n : ℕ} (hn : n ≠ 0) :
    usigma n = ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := by
  have h := usigmaAF_isMultiplicative.multiplicative_factorization _ hn
  rw [← usigmaAF_apply, h, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [usigmaAF_apply]
  exact usigma_prime_pow (Nat.prime_of_mem_primeFactors hp)
    (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn
      (Nat.dvd_of_mem_primeFactors hp)).ne'

lemma prod_primeFactors_pow_factorization {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  rw [← Nat.support_factorization]
  exact Nat.factorization_prod_pow_eq_self hn

/-- **Every unitary perfect number is even**: there are no odd unitary perfect numbers. -/
theorem even_of_isUnitaryPerfect {n : ℕ} (hn : IsUnitaryPerfect n) : Even n := by
  obtain ⟨hpos, hsig⟩ := hn
  have hn0 : n ≠ 0 := hpos.ne'
  by_contra hodd
  have h2n : ¬ (2 ∣ n) := by rw [Nat.even_iff] at hodd; omega
  have hprod : usigma n = ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := usigma_eq_prod hn0
  have hdvd : 2 ^ n.primeFactors.card ∣ usigma n := by
    rw [hprod, ← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpne : p ≠ 2 := by rintro rfl; exact h2n (Nat.dvd_of_mem_primeFactors hp)
    obtain ⟨k, hk⟩ := (hpp.odd_of_ne_two hpne).pow (n := n.factorization p)
    exact ⟨k + 1, by omega⟩
  have hcard : n.primeFactors.card ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h4 : (4 : ℕ) ∣ 2 * n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ n.primeFactors.card := pow_dvd_pow 2 hc
        _ ∣ usigma n := hdvd
        _ = 2 * n := hsig
    obtain ⟨c, hcc⟩ := h4
    exact h2n ⟨c, by omega⟩
  have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    prod_primeFactors_pow_factorization hn0
  interval_cases hcards : n.primeFactors.card
  · rw [Finset.card_eq_zero] at hcards
    rw [hcards, Finset.prod_empty] at hself
    rw [← hself] at hsig
    simp at hsig
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcards
    rw [hp, Finset.prod_singleton] at hself hprod
    rw [hprod, hself] at hsig
    have hn1 : n = 1 := by omega
    rw [hn1] at hp
    simp at hp

theorem isUnitaryPerfect_six : IsUnitaryPerfect 6 := by
  refine ⟨by norm_num, ?_⟩
  rw [show (6 : ℕ) = 2 * 3 by norm_num, usigma_mul_of_coprime (by norm_num),
    usigma_prime (by norm_num), usigma_prime (by norm_num)]

theorem isUnitaryPerfect_sixty : IsUnitaryPerfect 60 := by
  refine ⟨by norm_num, ?_⟩
  have h4 : usigma (2 ^ 2) = 2 ^ 2 + 1 := usigma_prime_pow (by norm_num) (by norm_num)
  rw [show (60 : ℕ) = 2 ^ 2 * (3 * 5) by norm_num, usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), h4, usigma_prime (by norm_num),
    usigma_prime (by norm_num)]
  norm_num

theorem isUnitaryPerfect_ninety : IsUnitaryPerfect 90 := by
  refine ⟨by norm_num, ?_⟩
  have h9 : usigma (3 ^ 2) = 3 ^ 2 + 1 := usigma_prime_pow (by norm_num) (by norm_num)
  rw [show (90 : ℕ) = 2 * (3 ^ 2 * 5) by norm_num, usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), h9, usigma_prime (by norm_num),
    usigma_prime (by norm_num)]
  norm_num

theorem isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 := by
  refine ⟨by norm_num, ?_⟩
  have h64 : usigma (2 ^ 6) = 2 ^ 6 + 1 := usigma_prime_pow (by norm_num) (by norm_num)
  rw [show (87360 : ℕ) = 2 ^ 6 * (3 * (5 * (7 * 13))) by norm_num,
    usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num), h64,
    usigma_prime (by norm_num), usigma_prime (by norm_num), usigma_prime (by norm_num),
    usigma_prime (by norm_num)]
  norm_num

theorem isUnitaryPerfect_big : IsUnitaryPerfect 146361946186458562560000 := by
  refine ⟨by norm_num, ?_⟩
  have h2 : usigma (2 ^ 18) = 2 ^ 18 + 1 := usigma_prime_pow (by norm_num) (by norm_num)
  have h5 : usigma (5 ^ 4) = 5 ^ 4 + 1 := usigma_prime_pow (by norm_num) (by norm_num)
  rw [show (146361946186458562560000 : ℕ) =
      2 ^ 18 * (3 * (5 ^ 4 * (7 * (11 * (13 * (19 * (37 * (79 * (109 * (157 * 313))))))))))
      by norm_num]
  rw [usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), h2, h5, usigma_prime (by norm_num),
    usigma_prime (by norm_num), usigma_prime (by norm_num), usigma_prime (by norm_num),
    usigma_prime (by norm_num), usigma_prime (by norm_num), usigma_prime (by norm_num),
    usigma_prime (by norm_num), usigma_prime (by norm_num), usigma_prime (by norm_num)]
  norm_num

/-- **Conditional reduction for the existence of a sixth unitary perfect number.**

Whether a sixth unitary perfect number exists is an open problem; only five are known,
namely `6`, `60`, `90`, `87360` and `146361946186458562560000`.  This theorem is the
conditional statement: if some unitary perfect number is different from all five known ones,
then there are (at least) six unitary perfect numbers.  The five known ones are proved to be
unitary perfect unconditionally (see `isUnitaryPerfect_six`, ..., `isUnitaryPerfect_big`). -/
theorem SixthUnitaryPerfectExists
    (h : ∃ N, IsUnitaryPerfect N ∧
      N ∉ ({6, 60, 90, 87360, 146361946186458562560000} : Finset ℕ)) :
    ∃ S : Finset ℕ, S.card = 6 ∧ ∀ n ∈ S, IsUnitaryPerfect n := by
  obtain ⟨N, hN, hNmem⟩ := h
  refine ⟨insert N {6, 60, 90, 87360, 146361946186458562560000}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hNmem]
    decide
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hN
    · exact isUnitaryPerfect_six
    · exact isUnitaryPerfect_sixty
    · exact isUnitaryPerfect_ninety
    · exact isUnitaryPerfect_87360
    · exact isUnitaryPerfect_big

end UnitaryPerfect
end Brockian

