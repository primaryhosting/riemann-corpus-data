import Mathlib

namespace Brockian.OddPerfectThreePrimes

open Finset

/-- A geometric-sum identity: `(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/
lemma geomSum_mul_pred (p a : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) + 1 = p ^ (a + 1) := by
  have h := geom_sum_mul (x := (p : ℤ)) (n := a + 1)
  simp at h
  have h2 : (∑ i ∈ Finset.range (a + 1), (p : ℤ) ^ i) = (∑ i ∈ Finset.range (a + 1), p ^ i : ℕ) := by simp
  rw [h2] at h
  have h3 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  have h4 : ((∑ i ∈ Finset.range (a + 1), p ^ i : ℕ) * (p - 1 : ℕ) + 1 : ℤ) = (p ^ (a + 1) : ℤ) := by
    simp only [h3]
    linarith
  exact_mod_cast h4

/-- For `p ≥ 3` and `q ≥ 5` we have `p * q ≤ 2 * ((p - 1) * (q - 1))`. -/
lemma prime_pair_bound {p q : ℕ} (hp : 3 ≤ p) (hq : 5 ≤ q) :
    p * q ≤ 2 * ((p - 1) * (q - 1)) := by
  have hp1 : p - 1 + 1 = p := by omega
  have hq1 : q - 1 + 1 = q := by omega
  calc p * q = (p - 1 + 1) * (q - 1 + 1) := by rw [hp1, hq1]
    _ = (p - 1) * (q - 1) + (p - 1) + (q - 1) + 1 := by ring
    _ ≤ (p - 1) * (q - 1) + (p - 1) * (q - 1) := by nlinarith
    _ = 2 * ((p - 1) * (q - 1)) := by ring

/-- A number of the shape `p ^ a * q ^ b` with `p ≥ 3`, `q ≥ 5` distinct primes has
sum of divisors less than twice itself. -/
lemma sum_divisors_lt_two_mul_of_two_primes {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) :
    ∑ d ∈ (p ^ a * q ^ b).divisors, d < 2 * (p ^ a * q ^ b) := by
  have hcoprime : Nat.Coprime (p ^ a) (q ^ b) := Nat.coprime_pow_primes a b hp hq hpq
  have h₁ : ∑ d ∈ (p ^ a).divisors, d = ∑ i ∈ Finset.range (a + 1), p ^ i := by
    rw [Nat.divisors_prime_pow hp]
    simp [Finset.sum_map]
  have h₂ : ∑ d ∈ (q ^ b).divisors, d = ∑ j ∈ Finset.range (b + 1), q ^ j := by
    rw [Nat.divisors_prime_pow hq]
    simp [Finset.sum_map]
  -- Multiplicativity of sum of divisors
  have hmul : ∑ d ∈ (p ^ a * q ^ b).divisors, d =
      (∑ d ∈ (p ^ a).divisors, d) * (∑ d ∈ (q ^ b).divisors, d) := by
    rw [Nat.divisors_mul]
    simp [Finset.mul_def]
    rw [Finset.sum_image]
    · rw [Finset.sum_product]
      simp [Finset.sum_mul_sum]
    · -- Need to prove injectivity: if p^i * q^j = p^k * q^l then (i,j) = (k,l)
      intro ⟨x₁, y₁⟩ hx₁ ⟨x₂, y₂⟩ hx₂ heq
      simp only [Finset.mem_coe, Finset.mem_product] at hx₁ hx₂
      rw [Nat.mem_divisors] at hx₁ hx₂
      simp only [Nat.mem_divisors] at hx₁ hx₂
      have h1 : x₁ ∣ p ^ a := hx₁.1.1
      have h2 : y₁ ∣ q ^ b := hx₁.2.1
      have h3 : x₂ ∣ p ^ a := hx₂.1.1
      have h4 : y₂ ∣ q ^ b := hx₂.2.1
      -- Divisors of p^a are p^i for i ≤ a
      rw [Nat.dvd_prime_pow hp] at h1 h3
      rw [Nat.dvd_prime_pow hq] at h2 h4
      -- Now h1 : ∃ k ≤ a, x₁ = p ^ k, etc.
      obtain ⟨i, hi, hx₁⟩ := h1
      obtain ⟨j, hj, hy₁⟩ := h2
      obtain ⟨k, hk, hx₂⟩ := h3
      obtain ⟨l, hl, hy₂⟩ := h4
      -- heq becomes p^i * q^j = p^k * q^l
      simp only [hx₁, hy₁, hx₂, hy₂] at heq
      -- From unique factorization, i = k and j = l
      have eq1 : i = k := by
        have h := congr_arg (·.factorization p) heq
        have hqp : q.factorization p = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          right; left
          exact fun hdvd => hpq (Nat.prime_dvd_prime_iff_eq hp hq |>.mp hdvd)
        simp [Nat.factorization_mul (pow_ne_zero i hp.ne_zero) (pow_ne_zero j hq.ne_zero),
              Nat.factorization_mul (pow_ne_zero k hp.ne_zero) (pow_ne_zero l hq.ne_zero),
              hp.factorization_self, hqp] at h
        exact h
      have eq2 : j = l := by
        have h := congr_arg (·.factorization q) heq
        have hpq' : p.factorization q = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          right; left
          exact fun hdvd => hpq (Nat.prime_dvd_prime_iff_eq hq hp |>.mp hdvd).symm
        simp [Nat.factorization_mul (pow_ne_zero i hp.ne_zero) (pow_ne_zero j hq.ne_zero),
              Nat.factorization_mul (pow_ne_zero k hp.ne_zero) (pow_ne_zero l hq.ne_zero),
              hpq', hq.factorization_self] at h
        exact h
      rw [hx₁, hx₂, eq1, hy₁, hy₂, eq2]
  -- Now combine: sum = (geom sum for p) * (geom sum for q)
  rw [hmul, h₁, h₂]
  -- Use geomSum_mul_pred
  have hp_ge_1 : 1 ≤ p := hp.one_lt.le
  have hpred_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hpred_pos' : 0 < q - 1 := Nat.sub_pos_of_lt hq.one_lt
  -- From geomSum_mul_pred: geom_sum * (p-1) + 1 = p^(a+1)
  -- So geom_sum = (p^(a+1) - 1) / (p - 1) < p^(a+1) / (p - 1)
  have geom_p : (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) + 1 = p ^ (a + 1) := geomSum_mul_pred p a hp_ge_1
  have geom_q : (∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1) + 1 = q ^ (b + 1) := geomSum_mul_pred q b hq.one_lt.le
  -- Bound the geometric sums
  have Sp_bound : (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) < p ^ (a + 1) := by omega
  have Sq_bound : (∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1) < q ^ (b + 1) := by omega
  -- Use prime_pair_bound
  have ppb := prime_pair_bound hp3 hq5
  -- Sp * Sq * (p-1) * (q-1) < p^(a+1) * q^(b+1)
  have prod_bound : (∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j) * ((p - 1) * (q - 1)) < p ^ (a + 1) * q ^ (b + 1) := by
    have step1 : ((∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1)) * ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) < p ^ (a + 1) * ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) :=
      Nat.mul_lt_mul_of_pos_right Sp_bound (by positivity)
    have step2 : p ^ (a + 1) * ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) < p ^ (a + 1) * q ^ (b + 1) :=
      Nat.mul_lt_mul_of_pos_left Sq_bound (by positivity)
    calc (∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j) * ((p - 1) * (q - 1))
        = ((∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1)) * ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) := by ring
      _ < p ^ (a + 1) * ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) := step1
      _ < p ^ (a + 1) * q ^ (b + 1) := step2
  -- p^(a+1) * q^(b+1) = p^a * q^b * (p * q)
  have expand : p ^ (a + 1) * q ^ (b + 1) = p ^ a * q ^ b * (p * q) := by ring
  rw [expand] at prod_bound
  -- From ppb: p * q ≤ 2 * ((p-1)*(q-1))
  -- So prod_bound: Sp * Sq * ((p-1)*(q-1)) < p^a * q^b * (p*q) ≤ p^a * q^b * 2 * ((p-1)*(q-1))
  have upper : p ^ a * q ^ b * (p * q) ≤ 2 * (p ^ a * q ^ b) * ((p - 1) * (q - 1)) := by
    calc p ^ a * q ^ b * (p * q) ≤ p ^ a * q ^ b * (2 * ((p - 1) * (q - 1))) := Nat.mul_le_mul_left _ ppb
      _ = 2 * (p ^ a * q ^ b) * ((p - 1) * (q - 1)) := by ring
  -- Combining
  have combined : (∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j) * ((p - 1) * (q - 1)) < 2 * (p ^ a * q ^ b) * ((p - 1) * (q - 1)) := lt_of_lt_of_le prod_bound upper
  -- Divide by ((p-1)*(q-1))
  have pos_prod : 0 < (p - 1) * (q - 1) := Nat.mul_pos hpred_pos hpred_pos'
  exact Nat.lt_of_mul_lt_mul_right combined

/-- Criterion for deficiency in terms of the sum of all divisors. -/
lemma deficient_of_sum_divisors_lt {n : ℕ}
    (h : ∑ d ∈ n.divisors, d < 2 * n) : Nat.Deficient n := by
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, two_mul] at h
  exact Nat.lt_of_add_lt_add_right h

/-- A number with prime factors exactly `{p, q}` factors as `p ^ a * q ^ b`. -/
lemma eq_pow_mul_pow_of_primeFactors_eq_pair {n p q : ℕ} (hn : n ≠ 0) (hpq : p ≠ q)
    (hS : n.primeFactors = {p, q}) :
    n = p ^ n.factorization p * q ^ n.factorization q := by
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  trans ∏ x ∈ n.primeFactors, x ^ n.factorization x
  · rfl
  · rw [hS]
    simp [Finset.prod_pair hpq]

/-- An odd prime factor is at least `3`. -/
lemma three_le_of_mem_primeFactors {n p : ℕ} (ho : Odd n) (hp : p ∈ n.primeFactors) :
    3 ≤ p := by
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hp_odd : Odd p := ho.of_dvd_nat hp_dvd
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_ge_two : 2 ≤ p := Nat.Prime.two_le hp_prime
  obtain ⟨k, hk⟩ := hp_odd
  omega

/-- An odd number whose set of prime factors is a pair `{p, q}` is deficient. -/
lemma odd_deficient_of_primeFactors_eq_pair {n p q : ℕ} (ho : Odd n) (hpq : p ≠ q)
    (hS : n.primeFactors = {p, q}) : Nat.Deficient n := by
  have hn : n ≠ 0 := by rintro rfl; simp at ho
  have hp_mem : p ∈ n.primeFactors := by rw [hS]; simp
  have hq_mem : q ∈ n.primeFactors := by rw [hS]; simp
  have hp3 : 3 ≤ p := three_le_of_mem_primeFactors ho hp_mem
  have hq3 : 3 ≤ q := three_le_of_mem_primeFactors ho hq_mem
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  -- Since `p ≠ q` and both are odd primes, one of them is at least 5
  have step (r : ℕ) (hr : r.Prime) (hr3 : 3 ≤ r) : r = 3 ∨ 5 ≤ r := by
    have h4 : r ≠ 4 := by rintro rfl; norm_num at hr
    omega
  have bound : (3 ≤ p ∧ 5 ≤ q) ∨ (5 ≤ p ∧ 3 ≤ q) := by
    rcases step p hp_prime hp3 with rfl | hp5
    · rcases step q hq_prime hq3 with rfl | hq5
      · exact absurd rfl hpq
      · exact Or.inl ⟨hp3, hq5⟩
    · exact Or.inr ⟨hp5, hq3⟩
  -- Rewrite n as p^a * q^b
  have hfactor : n = p ^ (n.factorization p) * q ^ (n.factorization q) :=
    eq_pow_mul_pow_of_primeFactors_eq_pair hn hpq hS
  -- Apply the bound
  rw [hfactor]
  rcases bound with ⟨hp3', hq5⟩ | ⟨hp5, hq3'⟩
  · exact deficient_of_sum_divisors_lt (sum_divisors_lt_two_mul_of_two_primes hp_prime hq_prime hpq hp3' hq5)
  · rw [mul_comm]
    exact deficient_of_sum_divisors_lt (sum_divisors_lt_two_mul_of_two_primes hq_prime hp_prime hpq.symm hq3' hp5)

/-- An odd natural number with at most two distinct prime factors is deficient. -/
lemma odd_deficient_of_primeFactors_card_le_two {n : ℕ} (ho : Odd n)
    (hc : n.primeFactors.card ≤ 2) : Nat.Deficient n := by
  have hn : n ≠ 0 := by rintro rfl; simp at ho
  interval_cases h : n.primeFactors.card
  · have : n = 1 := by
      have := Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp h)
      tauto
    simpa [this] using Nat.deficient_one
  · have : IsPrimePow n := isPrimePow_iff_card_primeFactors_eq_one.mpr h
    exact this.deficient
  · obtain ⟨p, q, hpq, hS⟩ := Finset.card_eq_two.mp h
    exact odd_deficient_of_primeFactors_eq_pair ho hpq hS

/-- An odd perfect number has at least three distinct prime factors. -/
theorem oddPerfect_three_primes {n : ℕ} (ho : Odd n) (hp : Nat.Perfect n) :
    3 ≤ n.primeFactors.card := by
  by_contra h
  have hc : n.primeFactors.card ≤ 2 := by omega
  have hd := odd_deficient_of_primeFactors_card_le_two ho hc
  exact (Nat.deficient_iff_not_abundant_and_not_perfect hp.2.ne').mp hd |>.2 hp

end Brockian.OddPerfectThreePrimes

