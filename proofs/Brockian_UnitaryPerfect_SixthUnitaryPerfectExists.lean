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

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- `sigmaStar n = σ*(n)` is the sum of the unitary divisors of `n`. -/
def sigmaStar (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is unitary perfect if it is positive and `σ*(n) = 2n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ sigmaStar n = 2 * n

/-- The five known unitary perfect numbers. -/
def knownUnitaryPerfect : Finset ℕ := {6, 60, 90, 87360, 146361946186458562560000}

lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ (d ∣ n ∧ n ≠ 0) ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

@[simp] lemma sigmaStar_one : sigmaStar 1 = 1 := by decide

lemma unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  ext d
  rw [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd, -⟩, hcop⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simp
    · have : i = k := by
        by_contra hne
        have hlt : i < k := lt_of_le_of_ne hi hne
        rw [Nat.pow_div hi hp.pos] at hcop
        have hdvd : p ∣ Nat.gcd (p ^ i) (p ^ (k - i)) :=
          Nat.dvd_gcd (dvd_pow_self p hipos.ne') (dvd_pow_self p (by omega))
        rw [hcop] at hdvd
        exact absurd (Nat.dvd_one.mp hdvd) hp.one_lt.ne'
      simp [this]
  · rintro (rfl | rfl)
    · exact ⟨⟨one_dvd _, pow_ne_zero k hp.pos.ne'⟩, by simp⟩
    · exact ⟨⟨dvd_rfl, pow_ne_zero k hp.pos.ne'⟩, by simp [Nat.div_self (pow_pos hp.pos k)]⟩

lemma sigmaStar_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    sigmaStar (p ^ k) = p ^ k + 1 := by
  have h1 : p ^ k ≠ 1 := by simp [hp.ne_one, hk]
  rw [sigmaStar, unitaryDivisors_prime_pow hp, Finset.sum_insert (by simp [Ne.symm h1]),
    Finset.sum_singleton]
  omega

lemma sigmaStar_prime {p : ℕ} (hp : p.Prime) : sigmaStar p = p + 1 := by
  simpa using sigmaStar_prime_pow (k := 1) hp one_ne_zero

/-- `σ*` is multiplicative. -/
lemma sigmaStar_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    sigmaStar (m * n) = sigmaStar m * sigmaStar n := by
  rw [sigmaStar, sigmaStar, sigmaStar, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (i := fun x => x.1 * x.2) (j := fun d => (Nat.gcd d m, Nat.gcd d n))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product] at hab
    obtain ⟨ha, hb⟩ := hab
    rw [mem_unitaryDivisors] at ha hb ⊢
    obtain ⟨⟨ham, -⟩, hac⟩ := ha
    obtain ⟨⟨hbn, -⟩, hbc⟩ := hb
    refine ⟨⟨mul_dvd_mul ham hbn, by positivity⟩, ?_⟩
    rw [← Nat.div_mul_div_comm ham hbn]
    exact Nat.Coprime.mul_left
      (Nat.Coprime.mul_right hac
        (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hbn)
          (Nat.Coprime.coprime_dvd_left ham h)))
      (Nat.Coprime.mul_right
        (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd ham)
          (Nat.Coprime.coprime_dvd_left hbn h.symm)) hbc)
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨⟨hdvd, -⟩, hcop⟩ := hd
    have hg : Nat.gcd d m ∣ m := Nat.gcd_dvd_right d m
    have hh : Nat.gcd d n ∣ n := Nat.gcd_dvd_right d n
    have hd_eq : Nat.gcd d m * Nat.gcd d n = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hdvd
    have hsplit : m / Nat.gcd d m * (n / Nat.gcd d n) = m * n / d := by
      rw [Nat.div_mul_div_comm hg hh, hd_eq]
    have h1 : Nat.Coprime (Nat.gcd d m) (m / Nat.gcd d m) :=
      Nat.Coprime.coprime_dvd_right (hsplit ▸ Dvd.intro _ rfl)
        (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left d m) hcop)
    have h2 : Nat.Coprime (Nat.gcd d n) (n / Nat.gcd d n) :=
      Nat.Coprime.coprime_dvd_right (hsplit ▸ Dvd.intro_left _ rfl)
        (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left d n) hcop)
    simp only [Finset.mem_product, mem_unitaryDivisors]
    exact ⟨⟨⟨hg, hm.ne'⟩, h1⟩, ⟨hh, hn.ne'⟩, h2⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨⟨ham, -⟩, -⟩, ⟨hbn, -⟩, -⟩ := hab
    have h1 : Nat.gcd (a * b) m = a := by
      rw [Nat.Coprime.gcd_mul_right_cancel a (Nat.Coprime.coprime_dvd_left hbn h.symm),
        Nat.gcd_eq_left ham]
    have h2 : Nat.gcd (a * b) n = b := by
      rw [Nat.Coprime.gcd_mul_left_cancel b (Nat.Coprime.coprime_dvd_left ham h),
        Nat.gcd_eq_left hbn]
    simp [h1, h2]
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hd.1.1
  · rintro ⟨a, b⟩ _
    rfl

/-- `σ*` of a product of powers of distinct primes. -/
lemma sigmaStar_prod_prime_pow (s : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ s, p.Prime) (he : ∀ p ∈ s, e p ≠ 0) :
    sigmaStar (∏ p ∈ s, p ^ e p) = ∏ p ∈ s, (p ^ e p + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hpa : a.Prime := hp a (Finset.mem_insert_self a s)
    have hps : ∀ p ∈ s, p.Prime := fun p hp' => hp p (Finset.mem_insert_of_mem hp')
    have hes : ∀ p ∈ s, e p ≠ 0 := fun p hp' => he p (Finset.mem_insert_of_mem hp')
    have hposprod : 0 < ∏ p ∈ s, p ^ e p :=
      Finset.prod_pos fun p hp' => pow_pos (hps p hp').pos _
    have hcop : Nat.Coprime (a ^ e a) (∏ p ∈ s, p ^ e p) := by
      refine Nat.Coprime.pow_left _ (Nat.Coprime.prod_right fun p hp' => ?_)
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hpa (hps p hp')).2
        (by rintro rfl; exact ha hp'))
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      sigmaStar_mul_of_coprime (pow_pos hpa.pos _) hposprod hcop,
      sigmaStar_prime_pow hpa (he a (Finset.mem_insert_self a s)), ih hps hes]

/-- The product formula for `σ*`: `σ*(n) = ∏_{p ∣ n} (p ^ v_p(n) + 1)`. -/
lemma sigmaStar_eq_prod {n : ℕ} (hn : n ≠ 0) :
    sigmaStar n = ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := by
  have hfac : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.factorization_prod_pow_eq_self hn
  calc sigmaStar n = sigmaStar (∏ p ∈ n.primeFactors, p ^ n.factorization p) := by rw [hfac]
    _ = ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := by
        refine sigmaStar_prod_prime_pow _ _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
          (fun p hp => ?_)
        rw [← Nat.support_factorization] at hp
        exact Finsupp.mem_support_iff.1 hp

/-- Main reduction: the existence of a sixth unitary perfect number is equivalent to the
existence of a finite set of primes together with positive exponents satisfying the explicit
multiplicative equation `∏ (p ^ e p + 1) = 2 * ∏ p ^ e p`, whose value is different from the
five known unitary perfect numbers.

(Whether a sixth unitary perfect number exists is an open problem; this is a reduction of the
question to a concrete arithmetic search over finite sets of prime powers.) -/
theorem SixthUnitaryPerfectExists :
    (∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect) ↔
      ∃ (s : Finset ℕ) (e : ℕ → ℕ), (∀ p ∈ s, p.Prime) ∧ (∀ p ∈ s, e p ≠ 0) ∧
        ∏ p ∈ s, (p ^ e p + 1) = 2 * ∏ p ∈ s, p ^ e p ∧
        ∏ p ∈ s, p ^ e p ∉ knownUnitaryPerfect := by
  constructor
  · rintro ⟨n, ⟨hpos, hn⟩, hnot⟩
    have hfac : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
      simpa [Finsupp.prod, Nat.support_factorization] using
        Nat.factorization_prod_pow_eq_self hpos.ne'
    refine ⟨n.primeFactors, fun p => n.factorization p,
      fun p hp => Nat.prime_of_mem_primeFactors hp, fun p hp => ?_, ?_, ?_⟩
    · rw [← Nat.support_factorization] at hp
      exact Finsupp.mem_support_iff.1 hp
    · rw [hfac, ← sigmaStar_eq_prod hpos.ne', hn]
    · rwa [hfac]
  · rintro ⟨s, e, hp, he, heq, hnot⟩
    refine ⟨∏ p ∈ s, p ^ e p, ⟨Finset.prod_pos fun p hp' => pow_pos (hp p hp').pos _, ?_⟩, hnot⟩
    rw [sigmaStar_prod_prime_pow s e hp he, heq]

end Brockian.UnitaryPerfect

