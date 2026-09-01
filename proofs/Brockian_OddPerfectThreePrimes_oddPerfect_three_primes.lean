import Mathlib
namespace Brockian.OddPerfectThreePrimes

open Finset

/-- For a prime `p`, `(p-1) * σ₁(p^a) = p^(a+1) - 1 < p * p^a`. -/
private lemma sigma_primePow_bound {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (p - 1) * (∑ d ∈ (p ^ a).divisors, d) < p * p ^ a := by
  have hdiv : (p ^ a).divisors = Finset.image (fun i => p ^ i) (Finset.range (a + 1)) := by
    ext x
    simp [Nat.divisors_prime_pow hp]
  rw [hdiv]
  rw [Finset.sum_image]
  · have hp1 : 1 < p := hp.one_lt
    have hsum : (p - 1) * (∑ x ∈ Finset.range (a + 1), p ^ x) = p ^ (a + 1) - 1 := by
      induction a + 1 with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, pow_succ]
        rw [mul_add, ih]
        have h1 : p ^ n - 1 + (p - 1) * p ^ n = p ^ n * p - 1 := by
          have h2 : (p - 1) * p ^ n + p ^ n = p * p ^ n := by
            have := Nat.sub_add_cancel hp.one_lt.le
            calc (p - 1) * p ^ n + p ^ n = ((p - 1) + 1) * p ^ n := by ring
              _ = p * p ^ n := by rw [this]
          calc p ^ n - 1 + (p - 1) * p ^ n
                = (p - 1) * p ^ n + (p ^ n - 1) := by ring
            _ = (p - 1) * p ^ n + p ^ n - 1 := by rw [Nat.add_sub_assoc (Nat.one_le_pow n p hp.pos)]
            _ = p * p ^ n - 1 := by rw [h2]
            _ = p ^ n * p - 1 := by rw [mul_comm]
        exact h1
    rw [hsum]
    rw [pow_succ]
    rw [mul_comm]
    exact Nat.sub_lt (mul_pos hp.pos (pow_pos hp.pos _)) zero_lt_one
  · intro i hi j hj h
    exact Nat.pow_right_injective hp.one_lt h

/-- The sum-of-divisors function is multiplicative over a finite family of pairwise coprime,
nonzero numbers. -/
private lemma sum_divisors_prod (s : Finset ℕ) (f : ℕ → ℕ) :
    (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Nat.Coprime (f p) (f q)) → (∀ p ∈ s, f p ≠ 0) →
    ∑ d ∈ (∏ p ∈ s, f p).divisors, d = ∏ p ∈ s, ∑ d ∈ (f p).divisors, d := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert a s ha ih =>
    intro hcop hne
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcop_a : Nat.Coprime (f a) (∏ p ∈ s, f p) :=
      Nat.Coprime.prod_right fun q hq =>
        hcop a (Finset.mem_insert_self a s) q (Finset.mem_insert_of_mem hq)
          (by rintro rfl; exact ha hq)
    rw [Nat.Coprime.sum_divisors_mul hcop_a,
      ih (fun p hp q hq hpq =>
            hcop p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq)
         (fun p hp => hne p (Finset.mem_insert_of_mem hp))]

/-- Multiplicative bound: `(∏ (p-1)) * σ₁(n) < (∏ p) * n` for `n` with at least one prime
factor. -/
private lemma sigma_prod_bound {n : ℕ} (hn : n ≠ 0) (hne : n.primeFactors.Nonempty) :
    (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
      < (∏ p ∈ n.primeFactors, p) * n := by
  -- Prime powers at different primes are coprime
  have hcoprime : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ≠ q →
      Nat.Coprime (p ^ (n.factorization p)) (q ^ (n.factorization q)) := by
    intro p hp q hq hneq
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hqq : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    exact Nat.coprime_pow_primes _ _ hpp hqq hneq
  -- All prime powers are positive
  have hpos : ∀ p ∈ n.primeFactors, 0 < p ^ (n.factorization p) := by
    intro p hp
    exact pow_pos (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)) _
  have hsum_divisors : ∑ d ∈ n.divisors, d
      = ∏ p ∈ n.primeFactors, ∑ d ∈ (p ^ (n.factorization p)).divisors, d := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    exact sum_divisors_prod _ _ hcoprime (fun p hp => (hpos p hp).ne')
  -- Now use hsum_divisors to complete the proof
  rw [hsum_divisors]
  -- Use sigma_primePow_bound for each factor
  have h_bound : ∏ p ∈ n.primeFactors, ((p - 1) * ∑ d ∈ (p ^ (n.factorization p)).divisors, d) <
      ∏ p ∈ n.primeFactors, p * p ^ (n.factorization p) := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro p hp
      have hp_pos : 0 < p := Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)
      have hsum_pos : 0 < ∑ d ∈ (p ^ (n.factorization p)).divisors, d := by
        apply Finset.sum_pos
        · intro d hd
          exact Nat.pos_of_mem_divisors hd
        · exact ⟨1, Nat.one_mem_divisors.mpr (pow_ne_zero _ hp_pos.ne')⟩
      exact Nat.mul_pos (Nat.sub_pos_of_lt (Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hp))) hsum_pos
    · intro p hp
      exact sigma_primePow_bound (Nat.prime_of_mem_primeFactors hp) (n.factorization p)
    · exact hne
  rw [Finset.prod_mul_distrib] at h_bound
  -- Now show that (∏ p) * (∏ p^a) = (∏ p) * n
  have hprod_eq : ∏ p ∈ n.primeFactors, p * p ^ (n.factorization p) =
      (∏ p ∈ n.primeFactors, p) * (∏ p ∈ n.primeFactors, p ^ (n.factorization p)) :=
    Finset.prod_mul_distrib
  have hprod_pow : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n :=
    Nat.prod_factorization_pow_eq_self hn
  rw [hprod_eq, hprod_pow] at h_bound
  exact h_bound

/-- If a finite set of integers `≥ 3` has at most two elements, then `∏ p ≤ 2 * ∏ (p-1)`. -/
private lemma prod_le_two_mul_prod_pred {S : Finset ℕ} (hS : S.card ≤ 2)
    (h3 : ∀ p ∈ S, 3 ≤ p) : (∏ p ∈ S, p) ≤ 2 * ∏ p ∈ S, (p - 1) := by
  by_cases hc : S.card = 0
  · have hS : S = ∅ := Finset.card_eq_zero.mp hc
    simp [hS]
  · by_cases hc1 : S.card = 1
    · rcases Finset.card_eq_one.mp hc1 with ⟨p, hp⟩
      subst hp
      simp only [Finset.prod_singleton]
      have := h3 p (Finset.mem_singleton_self p)
      omega
    · have hc2 : S.card = 2 := by omega
      rcases Finset.card_eq_two.mp hc2 with ⟨a, b, hab, rfl⟩
      have ha : 3 ≤ a := h3 a (by simp)
      have hb : 3 ≤ b := h3 b (by simp)
      rw [Finset.prod_pair hab, Finset.prod_pair hab]
      obtain ⟨x, rfl⟩ : ∃ x, a = x + 3 := ⟨a - 3, by omega⟩
      obtain ⟨y, rfl⟩ : ∃ y, b = y + 3 := ⟨b - 3, by omega⟩
      have e1 : x + 3 - 1 = x + 2 := by omega
      have e2 : y + 3 - 1 = y + 2 := by omega
      rw [e1, e2]
      have hxy : 1 ≤ x + y := by
        rcases Nat.eq_zero_or_pos x with hx | hx
        · subst hx
          have : y ≠ 0 := by rintro rfl; exact hab rfl
          omega
        · omega
      nlinarith [hxy]

/-- An odd perfect number has at least three distinct prime factors. -/
theorem oddPerfect_three_primes {n : ℕ} (ho : Odd n) (hp : Nat.Perfect n) :
    3 ≤ n.primeFactors.card := by
  by_contra hcard
  rw [not_le] at hcard
  have hn0 : 0 < n := hp.2
  have hsum : ∑ i ∈ n.divisors, i = 2 * n :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hn0).mp hp
  have hn1 : 1 < n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn : n = 1 := by omega
      subst hn
      rw [Nat.divisors_one] at hsum
      simp at hsum
    · exact h
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn1
  have key := sigma_prod_bound hn0.ne' hne
  rw [hsum] at key
  have h3 : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hpm
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpm
    have hodd : Odd p := by
      rcases hdvd with ⟨c, rfl⟩
      exact (Nat.odd_mul.mp ho).1
    have hp2 : p ≠ 2 := by
      rintro rfl
      simp [Nat.odd_iff] at hodd
    have := hpp.two_le
    omega
  have hle := prod_le_two_mul_prod_pred (by omega : n.primeFactors.card ≤ 2) h3
  nlinarith [key, hle, hn0]

end Brockian.OddPerfectThreePrimes

