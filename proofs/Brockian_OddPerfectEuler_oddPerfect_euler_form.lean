/-
  Aristotle target — Euler's theorem on odd perfect numbers (a genuine hard partial
  result toward the ancient odd-perfect-number problem; existence remains OPEN).

  If n is odd and perfect, then n has Euler's form n = p^k * m^2 with p prime,
  p ≡ 1 (mod 4), k ≡ 1 (mod 4), and p ∤ m.
-/
import Mathlib

namespace Brockian.OddPerfectEuler

open ArithmeticFunction

private lemma exists_factor_mod_four_eq_two {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (h : (∏ x ∈ s, f x) % 4 = 2) :
    ∃ x ∈ s, f x % 4 = 2 := by
  have heven : (∏ x ∈ s, f x) % 2 = 0 := by omega
  have hnot4 : ¬(4 ∣ ∏ x ∈ s, f x) := by omega
  have hex : ∃ x ∈ s, f x % 2 = 0 := by
    by_contra hall_odd
    push_neg at hall_odd
    have hall_odd' : ∀ x ∈ s, f x % 2 = 1 := fun x hx =>
      Nat.mod_two_ne_zero.mp (hall_odd x hx)
    have hprod_odd : (∏ x ∈ s, f x) % 2 = 1 := by
      have aux : ∀ t : Finset ι, (∀ x ∈ t, f x % 2 = 1) →
          (∏ x ∈ t, f x) % 2 = 1 := by
        intro t ht
        induction t using Finset.induction_on with
        | empty => simp
        | insert a s' ha ih =>
          simp [Finset.prod_insert ha]
          have ha_odd := ht a (Finset.mem_insert_self a s')
          have hs_odd := ih (fun x hx => ht x (Finset.mem_insert_of_mem hx))
          simp [Nat.mul_mod, ha_odd, hs_odd]
      exact aux s hall_odd'
    omega
  obtain ⟨x, hx, hfx_even⟩ := hex
  refine ⟨x, hx, ?_⟩
  have hfx_not4 : ¬(4 ∣ f x) := by
    intro h4
    apply hnot4
    exact dvd_trans h4 (Finset.dvd_prod_of_mem _ hx)
  omega

private lemma other_factor_odd {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (h : (∏ x ∈ s, f x) % 4 = 2)
    {x y : ι} (hx : x ∈ s) (hy : y ∈ s) (hfx : f x % 2 = 0) (hxy : y ≠ x) :
    f y % 2 = 1 := by
  -- If f y were even, combined with f x being even, the product would be 0 mod 4
  by_contra hfynotodd
  have hfyeven : f y % 2 = 0 := by omega
  -- The product f x * f y divides the total product, and is divisible by 4
  have hdiv : 4 ∣ (∏ z ∈ s, f z) := by
    have hprodxy : f x * f y ∣ ∏ z ∈ s, f z := by
      have hsub : {x, y} ⊆ s := by
        intro z hz
        simp at hz
        rcases hz with rfl | rfl <;> assumption
      rw [← Finset.prod_pair hxy.symm]
      exact Finset.prod_dvd_prod_of_subset (s := {x, y}) (t := s) (f := f) hsub
    have h4divxy : 4 ∣ f x * f y := by
      have : 2 ∣ f x := Nat.dvd_of_mod_eq_zero hfx
      have : 2 ∣ f y := Nat.dvd_of_mod_eq_zero hfyeven
      obtain ⟨a, ha⟩ := this
      have : 2 ∣ f x := Nat.dvd_of_mod_eq_zero hfx
      obtain ⟨b, hb⟩ := this
      use a * b
      rw [hb, ha]
      ring
    exact Nat.dvd_trans h4divxy hprodxy
  omega

private lemma geom_sum_parity {p e : ℕ} (hp : p % 2 = 1) :
    (∑ i ∈ Finset.range (e + 1), p ^ i) % 2 = (e + 1) % 2 := by
  have hpi : ∀ i, p ^ i % 2 = 1 := fun i => Nat.pow_mod p i 2 ▸ by simp [hp]
  simp [Finset.sum_nat_mod, hpi]

private lemma geom_sum_mod_four {p e : ℕ} (hp : p % 2 = 1)
    (h : (∑ i ∈ Finset.range (e + 1), p ^ i) % 4 = 2) :
    p % 4 = 1 ∧ e % 4 = 1 := by
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  cases hp4 with
  | inl hp1 =>
    refine ⟨hp1, ?_⟩
    have hpi : ∀ i, p ^ i % 4 = 1 := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => simp [pow_succ, Nat.mul_mod, ih, hp1]
    have hsum : (∑ i ∈ Finset.range (e + 1), p ^ i) % 4 = (e + 1) % 4 := by
      simp [Finset.sum_nat_mod, hpi]
    omega
  | inr hp3 =>
    -- p % 4 = 3 case leads to contradiction: sum is 0 or 1 mod 4, never 2
    have hpi : ∀ i, p ^ i % 4 = if i % 2 = 0 then 1 else 3 := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ, Nat.mul_mod, ih, hp3]
        split_ifs with hi <;> simp_all [Nat.add_mod]
    -- Now derive contradiction: sum is 0 or 1 mod 4, never 2
    have hsum_cycle : ∀ e, (∑ i ∈ Finset.range (e + 1), p ^ i) % 4 = if e % 2 = 0 then 1 else 0 := by
      intro e
      induction e with
      | zero => simp
      | succ e ih =>
        rw [Finset.sum_range_succ]
        rw [Nat.add_mod, ih, hpi (e + 1)]
        split_ifs <;> omega
    have := hsum_cycle e
    simp_all
    split_ifs at h with he <;> omega

private lemma exceptional_prime_data {n : ℕ} (hn : n ≠ 0) (hodd : Odd n)
    (hsigma : (sigma 1) n = 2 * n) :
    ∃ p ∈ n.primeFactors,
      (∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) % 4 = 2 ∧
      ∀ q ∈ n.primeFactors, q ≠ p → Even (n.factorization q) := by
  let f : ℕ → ℕ := fun p =>
    ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i
  have hprod : (∏ p ∈ n.primeFactors, f p) % 4 = 2 := by
    have heq : (∏ p ∈ n.primeFactors, f p) = 2 * n := by
      rw [← hsigma, sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
      simp [f]
    rw [heq]
    obtain ⟨a, rfl⟩ := hodd
    omega
  obtain ⟨p, hp, hp2⟩ :=
    exists_factor_mod_four_eq_two n.primeFactors f hprod
  refine ⟨p, hp, hp2, ?_⟩
  intro q hq hqp
  have hfp_even : f p % 2 = 0 := by omega
  have hfq_odd : f q % 2 = 1 :=
    other_factor_odd n.primeFactors f hprod hp hq hfp_even hqp
  have hqodd : q % 2 = 1 := by
    rw [← Nat.odd_iff]
    exact hodd.of_dvd_nat (Nat.mem_primeFactors.mp hq).2.1
  have hparity := geom_sum_parity (e := n.factorization q) hqodd
  rw [Nat.even_iff]
  dsimp [f] at hfq_odd
  omega

private lemma reconstruct_euler_factorization {n p k : ℕ}
    (hn : n ≠ 0) (hp : p.Prime) (hk : n.factorization p = k)
    (hother : ∀ q ∈ n.primeFactors, q ≠ p → Even (n.factorization q)) :
    ∃ m : ℕ, ¬ p ∣ m ∧ n = p ^ k * m ^ 2 := by
  -- First, express n using its prime factorization
  have hprod : n = ∏ q ∈ n.primeFactors, q ^ n.factorization q :=
    Eq.symm (Nat.factorization_prod_pow_eq_self hn)
  by_cases hp_mem : p ∈ n.primeFactors
  · -- p is a prime factor
    -- Separate p from the product
    have hsplits : n = p ^ k * ∏ q ∈ n.primeFactors \ {p}, q ^ n.factorization q := by
      conv_lhs => rw [hprod]
      rw [← Finset.prod_sdiff (Finset.singleton_subset_iff.mpr hp_mem)]
      simp [Finset.prod_singleton]
      rw [hk]
      ring
    -- All primes in the set n.primeFactors \ {p} have even exponents
    have hall_even : ∀ q ∈ n.primeFactors \ {p}, Even (n.factorization q) := by
      intro q hq
      exact hother q (Finset.mem_sdiff.mp hq |>.1) (fun hqp => Finset.mem_singleton.not.mp (Finset.mem_sdiff.mp hq |>.2) hqp)
    -- Define m as the product over n.primeFactors \ {p}
    let m := ∏ q ∈ n.primeFactors \ {p}, q ^ (n.factorization q / 2)
    use m
    -- Show p ∤ m
    have hp_ne_m : ¬ p ∣ m := by
      rw [Nat.Prime.dvd_iff_not_coprime hp]
      push_neg
      apply Nat.Coprime.prod_right
      intro q hq
      refine hp.coprime_iff_not_dvd.mpr ?_
      intro hqdiv
      have hpq : p = q := by
        have : p ∣ q := hp.dvd_of_dvd_pow hqdiv
        exact (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq |>.1))).mp this
      exact Finset.mem_singleton.not.mp (Finset.mem_sdiff.mp hq |>.2) hpq.symm
    refine ⟨hp_ne_m, ?_⟩
    rw [hsplits]
    congr 1
    show ∏ q ∈ n.primeFactors \ {p}, q ^ n.factorization q = m ^ 2
    symm
    rw [pow_two]
    trans ∏ q ∈ n.primeFactors \ {p}, (q ^ (n.factorization q / 2)) * (q ^ (n.factorization q / 2))
    · rw [← Finset.prod_mul_distrib]
    · refine Finset.prod_congr rfl ?_
      intro q hq
      have heven := hall_even q hq
      rw [← pow_add]
      congr 1
      linarith [Nat.div_mul_cancel heven.two_dvd]
  · -- p is not a prime factor, so k = 0
    have hk0 : k = 0 := by
      have : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (fun h => hp_mem (Nat.mem_primeFactors.mpr ⟨hp, h, hn⟩))
      rw [← hk, this]
    -- All prime factors of n have even exponents, so n is a perfect square
    have hall_even : ∀ q ∈ n.primeFactors, Even (n.factorization q) := by
      intro q hq
      exact hother q hq (fun hqp => hp_mem (hqp.symm ▸ hq))
    -- Define m as the product of q^(n.factorization q / 2)
    let m := ∏ q ∈ n.primeFactors, q ^ (n.factorization q / 2)
    use m
    have hp_ne_m : ¬ p ∣ m := by
      rw [Nat.Prime.dvd_iff_not_coprime hp]
      push_neg
      apply Nat.Coprime.prod_right
      intro q hq
      refine hp.coprime_iff_not_dvd.mpr ?_
      intro hqdiv
      have : p ∣ q := hp.dvd_of_dvd_pow hqdiv
      have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)).mp this |>.symm
      exact hp_mem (hqp ▸ hq)
    refine ⟨hp_ne_m, ?_⟩
    simp [hk0]
    rw [hprod]
    symm
    show (∏ q ∈ n.primeFactors, q ^ (n.factorization q / 2)) ^ 2 = ∏ q ∈ n.primeFactors, q ^ n.factorization q
    rw [pow_two]
    trans ∏ q ∈ n.primeFactors, (q ^ (n.factorization q / 2)) * (q ^ (n.factorization q / 2))
    · rw [← Finset.prod_mul_distrib]
    · refine Finset.prod_congr rfl ?_
      intro q hq
      have heven := hall_even q hq
      rw [← pow_add]
      congr 1
      linarith [Nat.div_mul_cancel heven.two_dvd]

/-- **Euler's form for odd perfect numbers.** -/
theorem oddPerfect_euler_form {n : ℕ} (hodd : Odd n) (hperf : Nat.Perfect n) :
    ∃ p k m : ℕ, p.Prime ∧ p % 4 = 1 ∧ k % 4 = 1 ∧ ¬ p ∣ m ∧ n = p ^ k * m ^ 2 := by
  have hnpos : 0 < n := hperf.2
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  have hsigma : (sigma 1) n = 2 * n := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hnpos).mp hperf
  obtain ⟨p, hp_mem, hp_geom, hother⟩ := exceptional_prime_data hn hodd hsigma
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hpodd : p % 2 = 1 := by
    rw [← Nat.odd_iff]
    exact hodd.of_dvd_nat (Nat.mem_primeFactors.mp hp_mem).2.1
  obtain ⟨hp4, hk4⟩ := geom_sum_mod_four hpodd hp_geom
  obtain ⟨m, hpm, hform⟩ :=
    reconstruct_euler_factorization hn hp rfl hother
  exact ⟨p, n.factorization p, m, hp, hp4, hk4, hpm, hform⟩

end Brockian.OddPerfectEuler

