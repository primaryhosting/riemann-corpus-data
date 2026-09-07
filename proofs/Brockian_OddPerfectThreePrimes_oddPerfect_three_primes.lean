/-!
# Odd perfect numbers have at least three prime factors

This is the Lean 4.32 port of Aristotle run
`794c7ebe-1ca0-4904-b28e-111fec8c1216`. The only portability change removes an
obsolete simplification after `geom_sum_mul` and uses the current name
`Nat.prod_factorization_pow_eq_self`.
-/

import Mathlib

namespace Brockian.OddPerfectThreePrimes

open Finset

/-- A geometric-sum identity. -/
lemma geomSum_mul_pred (p a : Nat) (hp : 1 <= p) :
    (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) + 1 = p ^ (a + 1) := by
  have h := geom_sum_mul (x := (p : Int)) (n := a + 1)
  have h2 :
      (∑ i ∈ Finset.range (a + 1), (p : Int) ^ i) =
        (∑ i ∈ Finset.range (a + 1), p ^ i : Nat) := by
    simp
  rw [h2] at h
  have h3 : ((p - 1 : Nat) : Int) = (p : Int) - 1 := by omega
  have h4 :
      ((∑ i ∈ Finset.range (a + 1), p ^ i : Nat) * (p - 1 : Nat) + 1 : Int) =
        (p ^ (a + 1) : Int) := by
    simp only [h3]
    linarith
  exact_mod_cast h4

/-- For `p >= 3` and `q >= 5`, `p*q <= 2*(p-1)*(q-1)`. -/
lemma prime_pair_bound {p q : Nat} (hp : 3 <= p) (hq : 5 <= q) :
    p * q <= 2 * ((p - 1) * (q - 1)) := by
  have hp1 : p - 1 + 1 = p := by omega
  have hq1 : q - 1 + 1 = q := by omega
  calc
    p * q = (p - 1 + 1) * (q - 1 + 1) := by rw [hp1, hq1]
    _ = (p - 1) * (q - 1) + (p - 1) + (q - 1) + 1 := by ring
    _ <= (p - 1) * (q - 1) + (p - 1) * (q - 1) := by nlinarith
    _ = 2 * ((p - 1) * (q - 1)) := by ring

/-- A number of shape `p^a*q^b` for distinct odd primes is deficient. -/
lemma sum_divisors_lt_two_mul_of_two_primes
    {p q a b : Nat} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hp3 : 3 <= p) (hq5 : 5 <= q) :
    ∑ d ∈ (p ^ a * q ^ b).divisors, d < 2 * (p ^ a * q ^ b) := by
  have hcoprime : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.coprime_pow_primes a b hp hq hpq
  have h1 :
      ∑ d ∈ (p ^ a).divisors, d = ∑ i ∈ Finset.range (a + 1), p ^ i := by
    rw [Nat.divisors_prime_pow hp]
    simp [Finset.sum_map]
  have h2 :
      ∑ d ∈ (q ^ b).divisors, d = ∑ j ∈ Finset.range (b + 1), q ^ j := by
    rw [Nat.divisors_prime_pow hq]
    simp [Finset.sum_map]
  have hmul :
      ∑ d ∈ (p ^ a * q ^ b).divisors, d =
        (∑ d ∈ (p ^ a).divisors, d) * (∑ d ∈ (q ^ b).divisors, d) := by
    rw [Nat.divisors_mul]
    simp [Finset.mul_def]
    rw [Finset.sum_image]
    · rw [Finset.sum_product]
      simp [Finset.sum_mul_sum]
    · intro ⟨x1, y1⟩ hx1 ⟨x2, y2⟩ hx2 heq
      simp only [Finset.mem_coe, Finset.mem_product] at hx1 hx2
      rw [Nat.mem_divisors] at hx1 hx2
      simp only [Nat.mem_divisors] at hx1 hx2
      have hx1dvd : x1 ∣ p ^ a := hx1.1.1
      have hy1dvd : y1 ∣ q ^ b := hx1.2.1
      have hx2dvd : x2 ∣ p ^ a := hx2.1.1
      have hy2dvd : y2 ∣ q ^ b := hx2.2.1
      rw [Nat.dvd_prime_pow hp] at hx1dvd hx2dvd
      rw [Nat.dvd_prime_pow hq] at hy1dvd hy2dvd
      obtain ⟨i, hi, hx1⟩ := hx1dvd
      obtain ⟨j, hj, hy1⟩ := hy1dvd
      obtain ⟨k, hk, hx2⟩ := hx2dvd
      obtain ⟨l, hl, hy2⟩ := hy2dvd
      simp only [hx1, hy1, hx2, hy2] at heq
      have eq1 : i = k := by
        have h := congr_arg (fun n => n.factorization p) heq
        have hqp : q.factorization p = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          right
          left
          exact fun hdvd =>
            hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
        simp [Nat.factorization_mul (pow_ne_zero i hp.ne_zero)
              (pow_ne_zero j hq.ne_zero),
            Nat.factorization_mul (pow_ne_zero k hp.ne_zero)
              (pow_ne_zero l hq.ne_zero), hp.factorization_self, hqp] at h
        exact h
      have eq2 : j = l := by
        have h := congr_arg (fun n => n.factorization q) heq
        have hpq' : p.factorization q = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          right
          left
          exact fun hdvd =>
            hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd).symm
        simp [Nat.factorization_mul (pow_ne_zero i hp.ne_zero)
              (pow_ne_zero j hq.ne_zero),
            Nat.factorization_mul (pow_ne_zero k hp.ne_zero)
              (pow_ne_zero l hq.ne_zero), hpq', hq.factorization_self] at h
        exact h
      rw [hx1, hx2, eq1, hy1, hy2, eq2]
  rw [hmul, h1, h2]
  have hp_ge_1 : 1 <= p := hp.one_lt.le
  have hpred_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hpred_pos' : 0 < q - 1 := Nat.sub_pos_of_lt hq.one_lt
  have geom_p :
      (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) + 1 = p ^ (a + 1) :=
    geomSum_mul_pred p a hp_ge_1
  have geom_q :
      (∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1) + 1 = q ^ (b + 1) :=
    geomSum_mul_pred q b hq.one_lt.le
  have Sp_bound :
      (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) < p ^ (a + 1) := by
    omega
  have Sq_bound :
      (∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1) < q ^ (b + 1) := by
    omega
  have ppb := prime_pair_bound hp3 hq5
  have prod_bound :
      (∑ i ∈ Finset.range (a + 1), p ^ i) *
          (∑ j ∈ Finset.range (b + 1), q ^ j) * ((p - 1) * (q - 1)) <
        p ^ (a + 1) * q ^ (b + 1) := by
    have step1 :
        ((∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1)) *
            ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) <
          p ^ (a + 1) *
            ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) :=
      Nat.mul_lt_mul_of_pos_right Sp_bound (by positivity)
    have step2 :
        p ^ (a + 1) * ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) <
          p ^ (a + 1) * q ^ (b + 1) :=
      Nat.mul_lt_mul_of_pos_left Sq_bound (by positivity)
    calc
      (∑ i ∈ Finset.range (a + 1), p ^ i) *
          (∑ j ∈ Finset.range (b + 1), q ^ j) * ((p - 1) * (q - 1)) =
        ((∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1)) *
          ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) := by ring
      _ < p ^ (a + 1) *
          ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) := step1
      _ < p ^ (a + 1) * q ^ (b + 1) := step2
  have expand :
      p ^ (a + 1) * q ^ (b + 1) = p ^ a * q ^ b * (p * q) := by
    ring
  rw [expand] at prod_bound
  have upper :
      p ^ a * q ^ b * (p * q) <=
        2 * (p ^ a * q ^ b) * ((p - 1) * (q - 1)) := by
    calc
      p ^ a * q ^ b * (p * q) <=
          p ^ a * q ^ b * (2 * ((p - 1) * (q - 1))) :=
        Nat.mul_le_mul_left _ ppb
      _ = 2 * (p ^ a * q ^ b) * ((p - 1) * (q - 1)) := by ring
  have combined :
      (∑ i ∈ Finset.range (a + 1), p ^ i) *
          (∑ j ∈ Finset.range (b + 1), q ^ j) * ((p - 1) * (q - 1)) <
        2 * (p ^ a * q ^ b) * ((p - 1) * (q - 1)) :=
    lt_of_lt_of_le prod_bound upper
  have pos_prod : 0 < (p - 1) * (q - 1) :=
    Nat.mul_pos hpred_pos hpred_pos'
  exact Nat.lt_of_mul_lt_mul_right combined

/-- A divisor-sum bound implies deficiency. -/
lemma deficient_of_sum_divisors_lt {n : Nat}
    (h : ∑ d ∈ n.divisors, d < 2 * n) : Nat.Deficient n := by
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, two_mul] at h
  exact Nat.lt_of_add_lt_add_right h

/-- A number with prime factors exactly `{p,q}` has the expected factorization. -/
lemma eq_pow_mul_pow_of_primeFactors_eq_pair
    {n p q : Nat} (hn : n ≠ 0) (hpq : p ≠ q)
    (hS : n.primeFactors = {p, q}) :
    n = p ^ n.factorization p * q ^ n.factorization q := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  trans ∏ x ∈ n.primeFactors, x ^ n.factorization x
  · rfl
  · rw [hS]
    simp [Finset.prod_pair hpq]

/-- Every odd prime factor is at least three. -/
lemma three_le_of_mem_primeFactors
    {n p : Nat} (ho : Odd n) (hp : p ∈ n.primeFactors) : 3 <= p := by
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hp_odd : Odd p := ho.of_dvd_nat hp_dvd
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_ge_two : 2 <= p := hp_prime.two_le
  obtain ⟨k, hk⟩ := hp_odd
  omega

/-- An odd number with exactly two distinct prime factors is deficient. -/
lemma odd_deficient_of_primeFactors_eq_pair
    {n p q : Nat} (ho : Odd n) (hpq : p ≠ q)
    (hS : n.primeFactors = {p, q}) : Nat.Deficient n := by
  have hn : n ≠ 0 := by rintro rfl; simp at ho
  have hp_mem : p ∈ n.primeFactors := by rw [hS]; simp
  have hq_mem : q ∈ n.primeFactors := by rw [hS]; simp
  have hp3 : 3 <= p := three_le_of_mem_primeFactors ho hp_mem
  have hq3 : 3 <= q := three_le_of_mem_primeFactors ho hq_mem
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have step (r : Nat) (hr : r.Prime) (hr3 : 3 <= r) : r = 3 ∨ 5 <= r := by
    have h4 : r ≠ 4 := by rintro rfl; norm_num at hr
    omega
  have bound : (3 <= p ∧ 5 <= q) ∨ (5 <= p ∧ 3 <= q) := by
    rcases step p hp_prime hp3 with rfl | hp5
    · rcases step q hq_prime hq3 with rfl | hq5
      · exact absurd rfl hpq
      · exact Or.inl ⟨hp3, hq5⟩
    · exact Or.inr ⟨hp5, hq3⟩
  have hfactor : n = p ^ n.factorization p * q ^ n.factorization q :=
    eq_pow_mul_pow_of_primeFactors_eq_pair hn hpq hS
  rw [hfactor]
  rcases bound with ⟨hp3', hq5⟩ | ⟨hp5, hq3'⟩
  · exact deficient_of_sum_divisors_lt
      (sum_divisors_lt_two_mul_of_two_primes
        hp_prime hq_prime hpq hp3' hq5)
  · rw [mul_comm]
    exact deficient_of_sum_divisors_lt
      (sum_divisors_lt_two_mul_of_two_primes
        hq_prime hp_prime hpq.symm hq3' hp5)

/-- An odd number with at most two distinct prime factors is deficient. -/
lemma odd_deficient_of_primeFactors_card_le_two
    {n : Nat} (ho : Odd n) (hc : n.primeFactors.card <= 2) :
    Nat.Deficient n := by
  have hn : n ≠ 0 := by rintro rfl; simp at ho
  interval_cases h : n.primeFactors.card
  · have hn1 : n = 1 := by
      have := Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp h)
      tauto
    simpa [hn1] using Nat.deficient_one
  · have hpp : IsPrimePow n := isPrimePow_iff_card_primeFactors_eq_one.mpr h
    exact hpp.deficient
  · obtain ⟨p, q, hpq, hS⟩ := Finset.card_eq_two.mp h
    exact odd_deficient_of_primeFactors_eq_pair ho hpq hS

/-- Every odd perfect number has at least three distinct prime factors. -/
theorem oddPerfect_three_primes
    {n : Nat} (ho : Odd n) (hp : Nat.Perfect n) :
    3 <= n.primeFactors.card := by
  by_contra h
  have hc : n.primeFactors.card <= 2 := by omega
  have hd := odd_deficient_of_primeFactors_card_le_two ho hc
  exact (Nat.deficient_iff_not_abundant_and_not_perfect hp.2.ne').mp hd |>.2 hp

end Brockian.OddPerfectThreePrimes
