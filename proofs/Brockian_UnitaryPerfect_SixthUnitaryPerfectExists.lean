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
Note on the header: Lean 4 requires `import` commands to come first in a file, so the
required header comment is placed immediately after the single `import Mathlib` line.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- `d` is a *unitary divisor* of `n` when `d ∣ n` and `d` is coprime to `n / d`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- `sigmaStar n` is the sum of the unitary divisors of `n`, usually written `σ*(n)`. -/
def sigmaStar (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is *unitary perfect* if it is positive and the sum of its unitary divisors is `2 n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ sigmaStar n = 2 * n

lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ (d ∣ n ∧ n ≠ 0) ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

lemma sigmaStar_one : sigmaStar 1 = 1 := by decide

/-- σ* is multiplicative: for coprime `m` and `n`, `σ*(mn) = σ*(m) σ*(n)`. -/
lemma sigmaStar_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    sigmaStar (m * n) = sigmaStar m * sigmaStar n := by
  rw [sigmaStar, sigmaStar, sigmaStar, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun d => (Nat.gcd d m, Nat.gcd d n)) (j := fun x => x.1 * x.2)
    ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨⟨hdvd, -⟩, hcop⟩ := hd
    have hab : Nat.gcd d m * Nat.gcd d n = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hdvd
    have ham : Nat.gcd d m ∣ m := Nat.gcd_dvd_right _ _
    have hbn : Nat.gcd d n ∣ n := Nat.gcd_dvd_right _ _
    have hquot : m * n / d = (m / Nat.gcd d m) * (n / Nat.gcd d n) := by
      rw [Nat.div_mul_div_comm ham hbn, hab]
    simp only [Finset.mem_product, mem_unitaryDivisors]
    refine ⟨⟨⟨ham, hm⟩, ?_⟩, ⟨⟨hbn, hn⟩, ?_⟩⟩
    · refine Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) ?_
      refine Nat.Coprime.coprime_dvd_right ?_ hcop
      rw [hquot]
      exact Dvd.intro _ rfl
    · refine Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) ?_
      refine Nat.Coprime.coprime_dvd_right ?_ hcop
      rw [hquot]
      exact Dvd.intro_left _ rfl
  · intro x hx
    simp only [Finset.mem_product, mem_unitaryDivisors] at hx
    obtain ⟨⟨⟨ham, -⟩, hca⟩, ⟨hbn, -⟩, hcb⟩ := hx
    rw [mem_unitaryDivisors]
    refine ⟨⟨mul_dvd_mul ham hbn, mul_ne_zero hm hn⟩, ?_⟩
    rw [← Nat.div_mul_div_comm ham hbn]
    have h1 : Nat.Coprime x.1 (n / x.2) :=
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hbn)
        (Nat.Coprime.coprime_dvd_left ham h)
    have h2 : Nat.Coprime x.2 (m / x.1) :=
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd ham)
        (Nat.Coprime.coprime_dvd_left hbn h.symm)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hca h1) (Nat.Coprime.mul_right h2 hcb)
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hd.1.1
  · intro x hx
    simp only [Finset.mem_product, mem_unitaryDivisors] at hx
    obtain ⟨⟨⟨ham, -⟩, -⟩, ⟨hbn, -⟩, -⟩ := hx
    have e1 : Nat.gcd (x.1 * x.2) m = x.1 := by
      rw [mul_comm]
      exact Nat.gcd_mul_of_coprime_of_dvd (Nat.Coprime.coprime_dvd_left hbn h.symm) ham
    have e2 : Nat.gcd (x.1 * x.2) n = x.2 :=
      Nat.gcd_mul_of_coprime_of_dvd (Nat.Coprime.coprime_dvd_left ham h) hbn
    show (Nat.gcd (x.1 * x.2) m, Nat.gcd (x.1 * x.2) n) = x
    rw [e1, e2]
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hd.1.1).symm

/-- The only unitary divisors of a prime power `p ^ a` (`a ≥ 1`) are `1` and `p ^ a`. -/
lemma unitaryDivisors_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    unitaryDivisors (p ^ a) = {1, p ^ a} := by
  have hpa : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
  ext d
  rw [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hdvd, -⟩, hcop⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · exact Or.inl (pow_zero p)
    · right
      congr 1
      by_contra hne
      have hlt : i < a := lt_of_le_of_ne hi hne
      rw [Nat.pow_div hi hp.pos] at hcop
      have h1 : p ∣ p ^ i := dvd_pow_self p hipos.ne'
      have h2 : p ∣ p ^ (a - i) := dvd_pow_self p (by omega)
      have hd1 : p ∣ 1 := by rw [← hcop]; exact Nat.dvd_gcd h1 h2
      exact absurd (Nat.eq_one_of_dvd_one hd1) hp.one_lt.ne'
  · rintro (rfl | rfl)
    · exact ⟨⟨one_dvd _, by omega⟩, Nat.coprime_one_left _⟩
    · exact ⟨⟨dvd_rfl, by omega⟩, by simp [Nat.div_self (by omega : 0 < p ^ a)]⟩

lemma sigmaStar_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    sigmaStar (p ^ a) = 1 + p ^ a := by
  have hpa : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
  rw [sigmaStar, unitaryDivisors_prime_pow hp ha, Finset.sum_pair hpa.ne]

lemma sigmaStar_prime_pow_mul {p a m : ℕ} (hp : p.Prime) (ha : 0 < a) (hm : m ≠ 0)
    (hpm : ¬ p ∣ m) : sigmaStar (p ^ a * m) = (1 + p ^ a) * sigmaStar m := by
  have hco : Nat.Coprime (p ^ a) m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  rw [sigmaStar_mul_of_coprime (pow_ne_zero _ hp.pos.ne') hm hco, sigmaStar_prime_pow hp ha]

open Nat in
/-- Splitting off the largest power of the smallest prime factor. -/
lemma sigmaStar_minFac_decomp {m : ℕ} (hm : 1 < m) :
    ∃ a k : ℕ, 0 < a ∧ k ≠ 0 ∧ m = m.minFac ^ a * k ∧ ¬ m.minFac ∣ k ∧ k ∣ m ∧
      sigmaStar m = (1 + m.minFac ^ a) * sigmaStar k := by
  have hm0 : m ≠ 0 := by omega
  have hp : (m.minFac).Prime := Nat.minFac_prime (by omega)
  have hpos : 0 < m.factorization m.minFac :=
    hp.factorization_pos_of_dvd hm0 (Nat.minFac_dvd m)
  refine ⟨m.factorization m.minFac, ordCompl[m.minFac] m, hpos,
    (Nat.ordCompl_pos m.minFac hm0).ne', (Nat.ordProj_mul_ordCompl_eq_self m m.minFac).symm,
    Nat.not_dvd_ordCompl hp hm0, Nat.ordCompl_dvd m m.minFac, ?_⟩
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m m.minFac]
  exact sigmaStar_prime_pow_mul hp hpos (Nat.ordCompl_pos m.minFac hm0).ne'
    (Nat.not_dvd_ordCompl hp hm0)

/-- The sum of unitary divisors of an odd number bigger than one is even. -/
lemma even_sigmaStar_of_odd {m : ℕ} (hodd : ¬ 2 ∣ m) (hm : 1 < m) : 2 ∣ sigmaStar m := by
  obtain ⟨a, k, ha, hk, hmk, hpk, hkm, hs⟩ := sigmaStar_minFac_decomp hm
  have hp : (m.minFac).Prime := Nat.minFac_prime (by omega)
  have hpodd : m.minFac ≠ 2 := fun h => hodd (h ▸ Nat.minFac_dvd m)
  have h2 : ¬ 2 ∣ m.minFac ^ a := fun h =>
    hpodd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)).symm
  rw [hs]
  refine Dvd.dvd.mul_right ?_ _
  omega

/-- Every unitary perfect number is even: there is no odd unitary perfect number. -/
theorem even_of_unitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) : Even n := by
  obtain ⟨h, h2⟩ := h
  rw [even_iff_two_dvd]
  by_contra hodd
  have hn1 : n ≠ 1 := by
    rintro rfl
    rw [sigmaStar_one] at h2; omega
  have hn : 1 < n := by omega
  obtain ⟨a, k, ha, hk, hnk, hpk, hkn, hs⟩ := sigmaStar_minFac_decomp hn
  have hp : (n.minFac).Prime := Nat.minFac_prime hn1
  have hpodd : n.minFac ≠ 2 := fun hq => hodd (hq ▸ Nat.minFac_dvd n)
  have hpo : ¬ 2 ∣ n.minFac ^ a := fun hq =>
    hpodd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hq)).symm
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hk) with h1 | hk1
  · rw [← h1, sigmaStar_one, mul_one] at hs
    rw [hs] at h2
    rw [← h1, mul_one] at hnk
    rw [← hnk] at h2
    have : 1 < n.minFac ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
    omega
  · have hkodd : ¬ 2 ∣ k := fun hq => hodd (hq.trans hkn)
    have hck : 2 ∣ sigmaStar k := even_sigmaStar_of_odd hkodd hk1
    have hb : 2 ∣ 1 + n.minFac ^ a := by omega
    have h4 : 4 ∣ 2 * n := by
      rw [← h2, hs]
      exact (by norm_num : (4:ℕ) = 2 * 2) ▸ mul_dvd_mul hb hck
    omega

/-! ### The five known unitary perfect numbers -/

theorem unitaryPerfect_6 : IsUnitaryPerfect 6 := by
  constructor
  · norm_num
  · decide

theorem unitaryPerfect_60 : IsUnitaryPerfect 60 := by
  constructor
  · norm_num
  · decide

theorem unitaryPerfect_90 : IsUnitaryPerfect 90 := by
  constructor
  · norm_num
  · decide

theorem unitaryPerfect_87360 : IsUnitaryPerfect 87360 := by
  refine ⟨by norm_num, ?_⟩
  have h1 : (87360 : ℕ) = 2 ^ 6 * 1365 := by norm_num
  have h2 : (1365 : ℕ) = 3 ^ 1 * 455 := by norm_num
  have h3 : (455 : ℕ) = 5 ^ 1 * 91 := by norm_num
  have h4 : (91 : ℕ) = 7 ^ 1 * 13 := by norm_num
  have h5 : (13 : ℕ) = 13 ^ 1 * 1 := by norm_num
  rw [h1, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h2, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h3, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h4, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h5, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_one]
  norm_num

/-- The fifth known unitary perfect number,
`2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313`. -/
def fifth : ℕ := 146361946186458562560000

theorem unitaryPerfect_fifth : IsUnitaryPerfect fifth := by
  refine ⟨by norm_num [fifth], ?_⟩
  have h1 : fifth = 2 ^ 18 * 558326515909036875 := by norm_num [fifth]
  have h2 : (558326515909036875 : ℕ) = 3 ^ 1 * 186108838636345625 := by norm_num
  have h3 : (186108838636345625 : ℕ) = 5 ^ 4 * 297774141818153 := by norm_num
  have h4 : (297774141818153 : ℕ) = 7 ^ 1 * 42539163116879 := by norm_num
  have h5 : (42539163116879 : ℕ) = 11 ^ 1 * 3867196646989 := by norm_num
  have h6 : (3867196646989 : ℕ) = 13 ^ 1 * 297476665153 := by norm_num
  have h7 : (297476665153 : ℕ) = 19 ^ 1 * 15656666587 := by norm_num
  have h8 : (15656666587 : ℕ) = 37 ^ 1 * 423153151 := by norm_num
  have h9 : (423153151 : ℕ) = 79 ^ 1 * 5356369 := by norm_num
  have h10 : (5356369 : ℕ) = 109 ^ 1 * 49141 := by norm_num
  have h11 : (49141 : ℕ) = 157 ^ 1 * 313 := by norm_num
  have h12 : (313 : ℕ) = 313 ^ 1 * 1 := by norm_num
  rw [h1, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h2, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h3, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h4, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h5, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h6, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h7, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h8, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h9, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h10, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h11, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    h12, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_one]
  norm_num [fifth]

/-- The five known unitary perfect numbers. -/
def known : Finset ℕ := {6, 60, 90, 87360, fifth}

theorem unitaryPerfect_of_mem_known {n : ℕ} (hn : n ∈ known) : IsUnitaryPerfect n := by
  fin_cases hn
  exacts [unitaryPerfect_6, unitaryPerfect_60, unitaryPerfect_90, unitaryPerfect_87360,
    unitaryPerfect_fifth]

theorem known_card : known.card = 5 := by
  simp [known, fifth]

/-- **Conditional reduction.**  A sixth unitary perfect number, i.e. a unitary perfect number
other than the five known ones `6, 60, 90, 87360` and
`146361946186458562560000`, would give six distinct unitary perfect numbers, all of
which are necessarily even. -/
theorem SixthUnitaryPerfectExists
    (h : ∃ n : ℕ, IsUnitaryPerfect n ∧ n ∉ known) :
    ∃ S : Finset ℕ, S.card = 6 ∧ ∀ n ∈ S, IsUnitaryPerfect n ∧ Even n := by
  obtain ⟨n, hn, hnk⟩ := h
  refine ⟨insert n known, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hnk, known_card]
  · intro m hm
    rcases Finset.mem_insert.1 hm with rfl | hm
    · exact ⟨hn, even_of_unitaryPerfect hn⟩
    · exact ⟨unitaryPerfect_of_mem_known hm, even_of_unitaryPerfect (unitaryPerfect_of_mem_known hm)⟩

end Brockian.UnitaryPerfect

