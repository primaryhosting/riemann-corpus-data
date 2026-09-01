import Mathlib

namespace Brockian.EvenPerfectLastDigit

/-- The core of the Euclid--Euler argument.  If the exact power of two in a
perfect number is `2^k`, its odd part is the corresponding Mersenne prime. -/
theorem perfect_two_pow_mul_odd {k m : ℕ} (hk : 1 ≤ k) (hm : Odd m)
    (hp : Nat.Perfect (2 ^ k * m)) :
    m = 2 ^ (k + 1) - 1 ∧ Nat.Prime m := by
  rw [Nat.Perfect] at hp
  obtain ⟨hsum, hpos⟩ := hp
  -- Sum of divisors = sum of proper divisors + self
  have hsum_all : ∑ i ∈ (2 ^ k * m).divisors, i = 2 * (2 ^ k * m) := by
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp [hsum]
    ring
  -- Since gcd(2^k, m) = 1, sum of divisors is multiplicative
  have hgcd : Nat.gcd (2 ^ k) m = 1 := by
    have h2_coprime : Nat.Coprime 2 m := by
      apply Nat.prime_two.coprime_iff_not_dvd.mpr
      rw [Nat.dvd_iff_mod_eq_zero, Nat.odd_iff.mp hm]
      norm_num
    exact Nat.Coprime.pow_left k h2_coprime
  -- σ(2^k) = 2^(k+1) - 1
  have hmersenne : ∑ i ∈ (2 ^ k).divisors, i = 2 ^ (k + 1) - 1 := by
    rw [Nat.divisors_prime_pow Nat.prime_two]
    simp [Nat.geomSum_eq (by norm_num : 1 < 2)]
  -- σ is multiplicative for coprime numbers
  have hmultiplicative : (∑ i ∈ (2 ^ k * m).divisors, i) =
                         (∑ i ∈ (2 ^ k).divisors, i) * (∑ i ∈ m.divisors, i) := by
    have : Nat.Coprime (2 ^ k) m := Nat.coprime_iff_gcd_eq_one.mpr hgcd
    exact this.sum_divisors_mul
  -- Key equation: (2^(k+1) - 1) * σ(m) = 2^(k+1) * m
  have hkey : (2 ^ (k + 1) - 1) * (∑ i ∈ m.divisors, i) = 2 ^ (k + 1) * m := by
    calc (2 ^ (k + 1) - 1) * (∑ i ∈ m.divisors, i)
        = (∑ i ∈ (2 ^ k).divisors, i) * (∑ i ∈ m.divisors, i) := by rw [hmersenne]
      _ = (∑ i ∈ (2 ^ k * m).divisors, i) := hmultiplicative.symm
      _ = 2 * (2 ^ k * m) := hsum_all
      _ = 2 ^ (k + 1) * m := by ring
  -- m > 0
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
  -- σ(m) ≥ m + 1
  have hsigma_ge : ∑ i ∈ m.divisors, i ≥ m + 1 := by
    have hm_div : m ∣ m := Nat.dvd_refl m
    have h1_div : 1 ∣ m := Nat.one_dvd m
    have hm_mem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨hm_div, by omega⟩
    have h1_mem : 1 ∈ m.divisors := Nat.mem_divisors.mpr ⟨h1_div, by omega⟩
    calc ∑ i ∈ m.divisors, i
        ≥ ∑ i ∈ ({m, 1} : Finset ℕ), i := by
          apply Finset.sum_le_sum_of_subset
          simp [Finset.insert_subset_iff, hm_pos.ne']
      _ = m + 1 := by
          have hm_ne_1 : m ≠ 1 := by
            intro hm1
            simp [hm1] at hkey
            have : 2 ^ (k + 1) > 0 := pow_pos (by norm_num) _
            omega
          rw [Finset.sum_pair hm_ne_1]
  -- From hkey and hsigma_ge: m ≥ 2^(k+1) - 1
  have hpow_pos : 0 < 2 ^ (k + 1) := pow_pos (by norm_num) _
  have hm_ge : m ≥ 2 ^ (k + 1) - 1 := by
    have h1 : (2 ^ (k + 1) - 1) * (m + 1) ≤ (2 ^ (k + 1) - 1) * (∑ i ∈ m.divisors, i) := by
      apply Nat.mul_le_mul_left
      exact hsigma_ge
    have h2 : (2 ^ (k + 1) - 1) * (m + 1) ≤ 2 ^ (k + 1) * m := by
      rw [← hkey]
      exact h1
    -- Cast to Int: (2^(k+1) - 1) * (m + 1) ≤ 2^(k+1) * m
    have h2_int : ((2 : ℤ) ^ (k + 1) - 1) * (↑m + 1) ≤ (2 : ℤ) ^ (k + 1) * ↑m := by
      have h2' : (2 ^ (k + 1) - 1) * (m + 1) ≤ 2 ^ (k + 1) * m := h2
      have hcast : (2 : ℤ) ^ (k + 1) - 1 = ((2 ^ (k + 1) - 1 : ℕ) : ℤ) := by
        have : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
        simp
      rw [hcast]
      norm_cast
    -- Expanding: 2^(k+1)*m + 2^(k+1) - m - 1 ≤ 2^(k+1)*m
    -- So: 2^(k+1) - m - 1 ≤ 0, i.e., m ≥ 2^(k+1) - 1
    have hpow_pos_int : (0 : ℤ) < 2 ^ (k + 1) := by norm_cast
    nlinarith [hpow_pos_int, h2_int]
  -- From hkey: (2^(k+1) - 1) | 2^(k+1) * m
  -- Since gcd(2^(k+1) - 1, 2^(k+1)) = 1, we have (2^(k+1) - 1) | m
  have hcoprime : Nat.Coprime (2 ^ (k + 1) - 1) (2 ^ (k + 1)) := by
    have hle : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    apply Nat.coprime_of_dvd
    intro p pp d1 d2
    have h := Nat.dvd_sub d2 d1
    have heq : 2 ^ (k + 1) - (2 ^ (k + 1) - 1) = 1 := by omega
    rw [heq] at h
    exact pp.ne_one (Nat.eq_one_of_dvd_one h)
  have hdiv_prod : (2 ^ (k + 1) - 1) ∣ (2 ^ (k + 1)) * m := by
    have h1 : (2 ^ (k + 1) - 1) ∣ (2 ^ (k + 1) - 1) * (∑ i ∈ m.divisors, i) := 
      ⟨∑ i ∈ m.divisors, i, rfl⟩
    rwa [hkey] at h1
  have hdiv : (2 ^ (k + 1) - 1) ∣ m := Nat.Coprime.dvd_of_dvd_mul_left hcoprime hdiv_prod
  -- Combined with m ≥ 2^(k+1) - 1, we get m = 2^(k+1) - 1
  have hm_eq : m = 2 ^ (k + 1) - 1 := by
    obtain ⟨c, hc⟩ := hdiv
    simp_all
    rcases c with _ | c'
    · omega
    · -- c = c' + 1, so m = (c' + 1) * (2^(k+1) - 1)
      -- If c' = 0, then m = 2^(k+1) - 1, which is what we want
      -- If c' ≥ 1, we'll derive a contradiction
      rcases c' with _ | c''
      · -- c' = 0, so c = 1, and m = 2^(k+1) - 1
        simp
      · -- c' = c'' + 1 ≥ 1, so c = c'' + 2 ≥ 2
        -- We'll derive a contradiction
        -- From hkey: σ(m) = 2^(k+1)*(c'+1)
        -- Sum of proper divisors of m = σ(m) - m = (c'+1)
        -- But proper divisors include 1 and (c'+1), so sum ≥ 1 + (c'+1) = c' + 2 > c' + 1
        have hsigma_eq : ∑ x ∈ ((2 ^ (k + 1) - 1) * (c'' + 2)).divisors, x = 2 ^ (k + 1) * (c'' + 2) := by
          have : (2 ^ (k + 1) - 1) * (∑ x ∈ ((2 ^ (k + 1) - 1) * (c'' + 2)).divisors, x) = 
                 2 ^ (k + 1) * ((2 ^ (k + 1) - 1) * (c'' + 2)) := by simp_all
          have hpow_pos : 0 < 2 ^ (k + 1) - 1 := by
            have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
            omega
          nlinarith [hpow_pos]
        have hproper_sum : ∑ x ∈ ((2 ^ (k + 1) - 1) * (c'' + 2)).properDivisors, x = c'' + 2 := by
          have htotal : ∑ x ∈ ((2 ^ (k + 1) - 1) * (c'' + 2)).divisors, x = 
                        ∑ x ∈ ((2 ^ (k + 1) - 1) * (c'' + 2)).properDivisors, x + ((2 ^ (k + 1) - 1) * (c'' + 2)) := by
            rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
          have hdiff : 2 ^ (k + 1) * (c'' + 2) - (2 ^ (k + 1) - 1) * (c'' + 2) = c'' + 2 := by
            rw [← Nat.mul_sub_right_distrib]
            have h1 : 2 ^ (k + 1) - (2 ^ (k + 1) - 1) = 1 := by
              have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
              omega
            simp [h1]
          omega
        -- 2^(k+1) - 1 ≥ 2 for k ≥ 1
        have hmersenne : 1 < 2 ^ (k + 1) - 1 := by
          have h1 : 4 ≤ 2 ^ (k + 1) := by
            calc 4 = 2^2 := by norm_num
              _ ≤ 2^(k+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hm_pos : 0 < (2 ^ (k + 1) - 1) * (c'' + 2) := by
          apply Nat.mul_pos
          · have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
            omega
          · omega
        -- 1 is a proper divisor of m
        have h1_lt : 1 < (2 ^ (k + 1) - 1) * (c'' + 2) := by
          have : (2 ^ (k + 1) - 1) ≥ 2 := by omega
          have : (c'' + 2) ≥ 2 := by omega
          nlinarith
        have h1_div : 1 ∈ ((2 ^ (k + 1) - 1) * (c'' + 2)).properDivisors := by
          rw [Nat.mem_properDivisors]
          exact ⟨Nat.one_dvd _, h1_lt⟩
        -- c'' + 2 is a proper divisor of m (since c'' + 2 < m when 2^(k+1) - 1 ≥ 2 and c'' + 2 ≥ 2)
        have hc1_lt : c'' + 2 < (2 ^ (k + 1) - 1) * (c'' + 2) := by
          have h1 : (2 ^ (k + 1) - 1) ≥ 2 := by omega
          have h2 : (c'' + 2) ≥ 2 := by omega
          nlinarith
        have hc1_div : c'' + 2 ∈ ((2 ^ (k + 1) - 1) * (c'' + 2)).properDivisors := by
          rw [Nat.mem_properDivisors]
          exact ⟨⟨2 ^ (k + 1) - 1, by ring⟩, hc1_lt⟩
        -- 1 ≠ c'' + 2 since c'' ≥ 1 means c'' + 2 ≥ 3
        have h1_ne_c1 : (1 : ℕ) ≠ c'' + 2 := by omega
        have hsum_ge : ∑ x ∈ ((2 ^ (k + 1) - 1) * (c'' + 2)).properDivisors, x ≥ 1 + (c'' + 2) := by
          have hsub : ({1, c'' + 2} : Finset ℕ) ⊆ ((2 ^ (k + 1) - 1) * (c'' + 2)).properDivisors := by
            rw [Finset.insert_subset_iff]
            exact ⟨h1_div, Finset.singleton_subset_iff.mpr hc1_div⟩
          calc ∑ x ∈ ((2 ^ (k + 1) - 1) * (c'' + 2)).properDivisors, x
              ≥ ∑ x ∈ ({1, c'' + 2} : Finset ℕ), x := Finset.sum_le_sum_of_subset hsub
            _ = 1 + (c'' + 2) := by rw [Finset.sum_pair h1_ne_c1]
        linarith
  -- So m = 2^(k+1) - 1 and is prime
  -- We need to show Nat.Prime m
  -- From hkey: σ(m) = 2^(k+1)*(c'+1) where c = c'+1, but c = 1 in the valid case
  -- So σ(m) = 2^(k+1) = m + 1
  -- Sum of proper divisors = σ(m) - m = 1
  -- So m is prime
  have hprime : Nat.Prime m := by
    apply Nat.prime_def.mpr
    constructor
    · -- m > 1
      -- m = 2^(k+1) - 1 ≥ 4 - 1 = 3 > 1, so m ≥ 2
      have h1 : 4 ≤ 2 ^ (k + 1) := by
        calc 4 = 2^2 := by norm_num
          _ ≤ 2^(k+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · -- For all a, if a ∣ m, then a = 1 ∨ a = m
      intro a ha
      by_cases ha_eq : a = 1
      · left; exact ha_eq
      · right
        -- If a ≠ 1 and a ∣ m, then a = m
        -- Otherwise, a is a proper divisor, and sum of proper divisors ≥ 1 + a > 1 = sum
        have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos ha hm_pos
        by_contra ha_ne_m
        -- ha_ne_m : ¬(a = m), so a < m (since a ∣ m and a ≠ m)
        have ha_lt : a < m := Nat.lt_of_le_of_ne (Nat.le_of_dvd hm_pos ha) ha_ne_m
        have hsigma_m : ∑ x ∈ m.divisors, x = m + 1 := by
          have hpow_pos : 0 < 2 ^ (k + 1) - 1 := by
            have : 4 ≤ 2 ^ (k + 1) := by
              calc 4 = 2^2 := by norm_num
                _ ≤ 2^(k+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          have hkey' : (2 ^ (k + 1) - 1) * (∑ x ∈ m.divisors, x) = 2 ^ (k + 1) * m := hkey
          rw [hm_eq] at hkey' ⊢
          -- Now hkey' : (2^(k+1)-1) * σ(2^(k+1)-1) = 2^(k+1) * (2^(k+1)-1)
          -- Rewrite RHS to have same form
          have hkey'' : (2 ^ (k + 1) - 1) * (∑ x ∈ (2 ^ (k + 1) - 1).divisors, x) = 
                        (2 ^ (k + 1) - 1) * 2 ^ (k + 1) := by rw [hkey']; ring
          have h := Nat.eq_of_mul_eq_mul_left hpow_pos hkey''
          -- h : ∑ x ∈ (2^(k+1)-1).divisors, x = 2^(k+1)
          omega
        have hproper : ∑ x ∈ m.properDivisors, x = 1 := by
          have := @Nat.sum_divisors_eq_sum_properDivisors_add_self m
          omega
        have h1_mem : 1 ∈ m.properDivisors := by
          rw [Nat.mem_properDivisors]
          exact ⟨Nat.one_dvd _, by omega⟩
        have ha_mem : a ∈ m.properDivisors := by
          rw [Nat.mem_properDivisors]
          exact ⟨ha, ha_lt⟩
        have h1_ne_a : (1 : ℕ) ≠ a := by omega
        have hsum_ge : ∑ x ∈ m.properDivisors, x ≥ 1 + a := by
          have hsub : ({1, a} : Finset ℕ) ⊆ m.properDivisors := by
            rw [Finset.insert_subset_iff]
            exact ⟨h1_mem, Finset.singleton_subset_iff.mpr ha_mem⟩
          calc ∑ x ∈ m.properDivisors, x
              ≥ ∑ x ∈ ({1, a} : Finset ℕ), x := Finset.sum_le_sum_of_subset hsub
            _ = 1 + a := by rw [Finset.sum_pair h1_ne_a]
        omega
  exact ⟨hm_eq, hprime⟩

/-- Euclid--Euler classification, in the direction needed here: an even perfect
natural number is a power of two times the corresponding Mersenne prime. -/
theorem even_perfect_classification {n : ℕ} (he : Even n) (hp : Nat.Perfect n) :
    ∃ p : ℕ, Nat.Prime (2 ^ p - 1) ∧ n = 2 ^ (p - 1) * (2 ^ p - 1) := by
  rcases Nat.exists_eq_two_pow_mul_odd hp.2.ne' with ⟨k, m, hm, rfl⟩
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    exact (Nat.not_even_iff_odd.mpr hm) (by simpa using he)
  obtain ⟨hm_eq, hm_prime⟩ := perfect_two_pow_mul_odd hk hm hp
  refine ⟨k + 1, ?_, ?_⟩
  · simpa [hm_eq] using hm_prime
  · simp [hm_eq]

/-- A number in Euclid--Euler form has final decimal digit 6 or 8. -/
theorem euclidEuler_form_last_digit {p : ℕ} (hprime : Nat.Prime (2 ^ p - 1)) :
    (2 ^ (p - 1) * (2 ^ p - 1)) % 10 = 6 ∨
      (2 ^ (p - 1) * (2 ^ p - 1)) % 10 = 8 := by
  by_cases hp2 : p = 2
  · simp [hp2]
  · -- p ≥ 2 since 2^p - 1 is prime
    have hp_pos : 2 ≤ p := by
      by_contra h
      push_neg at h
      interval_cases p <;> simp_all [Nat.Prime]
    -- If p is even, 2^p - 1 is composite (since 2^p - 1 = (2^(p/2) - 1)(2^(p/2) + 1))
    have hp_odd : Odd p := by
      by_contra hp_even
      rw [Nat.not_odd_iff_even] at hp_even
      obtain ⟨k, hk⟩ := hp_even
      have hk_pos : k ≥ 2 := by omega
      -- 2^p - 1 = 2^(2k) - 1 = (2^k - 1)(2^k + 1)
      have hfactor : 2 ^ p - 1 = (2 ^ k - 1) * (2 ^ k + 1) := by
        rw [hk]
        have h1 : k + k = k * 2 := by ring
        rw [h1, pow_mul]
        have h2 : (2 ^ k) ^ 2 - 1 = (2 ^ k - 1) * (2 ^ k + 1) := by
          have : (2 ^ k) ^ 2 - 1 = (2 ^ k) ^ 2 - 1^2 := by norm_num
          rw [this, Nat.sq_sub_sq, mul_comm]
        exact h2
      have h1 : 1 < 2 ^ k - 1 := by
        have h4 : 2 ^ k ≥ 4 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hk_pos
        omega
      have h2 : 1 < 2 ^ k + 1 := by omega
      rw [hfactor] at hprime
      exact Nat.not_prime_mul h1.ne' h2.ne' hprime
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
      rcases hp_odd with ⟨m, hm⟩
      omega
    -- Since 2^p - 1 is prime, p ≠ 1
    have hp_ne_1 : p ≠ 1 := by
      intro hp1
      rw [hp1] at hprime
      norm_num at hprime
    -- For p % 4 = 1, we have p ≥ 5
    have hp5 : p % 4 = 1 → 5 ≤ p := by intro h; omega
    -- For p % 4 = 3, we have p ≥ 3
    have hp3 : p % 4 = 3 → 3 ≤ p := by intro h; omega
    -- Helper cycles
    have hcycle1 : ∀ k : ℕ, (2 ^ (4 * k + 1)) % 10 = 2 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have : 4 * (k + 1) + 1 = 4 * k + 1 + 4 := by ring
        rw [this, pow_add]
        calc (2 ^ (4 * k + 1) * 2 ^ 4) % 10 = (2 ^ (4 * k + 1) % 10 * (2 ^ 4 % 10)) % 10 := by rw [Nat.mul_mod]
          _ = (2 * 6) % 10 := by rw [ih]; norm_num
          _ = 2 := by norm_num
    have hcycle0 : ∀ k : ℕ, k ≥ 1 → (2 ^ (4 * k)) % 10 = 6 := by
      intro k hk
      have heq : 4 * k = 4 * (k - 1) + 1 + 3 := by omega
      rw [heq]
      rw [show (4 : ℕ) * (k - 1) + 1 + 3 = (4 * (k - 1) + 1) + 3 by ring]
      rw [pow_add]
      rw [Nat.mul_mod, hcycle1 (k - 1)]
      norm_num
    have hcycle2 : ∀ k : ℕ, (2 ^ (4 * k + 2)) % 10 = 4 := by
      intro k
      have : 4 * k + 2 = 4 * k + 1 + 1 := by ring
      rw [this, pow_add]
      calc (2 ^ (4 * k + 1) * 2 ^ 1) % 10 = (2 ^ (4 * k + 1) % 10 * (2 ^ 1 % 10)) % 10 := by rw [Nat.mul_mod]
        _ = (2 * 2) % 10 := by rw [hcycle1 k]; norm_num
        _ = 4 := by norm_num
    have hcycle3 : ∀ k : ℕ, (2 ^ (4 * k + 3)) % 10 = 8 := by
      intro k
      have : 4 * k + 3 = 4 * k + 2 + 1 := by ring
      rw [this, pow_add]
      calc (2 ^ (4 * k + 2) * 2 ^ 1) % 10 = (2 ^ (4 * k + 2) % 10 * (2 ^ 1 % 10)) % 10 := by rw [Nat.mul_mod]
        _ = (4 * 2) % 10 := by rw [hcycle2 k]; norm_num
        _ = 8 := by norm_num
    -- Now prove the main result
    rcases hp4 with hp4 | hp4
    · -- p % 4 = 1: product ends in 6
      left
      -- p - 1 ≡ 0 mod 4
      have hp1_mod : (p - 1) % 4 = 0 := by omega
      -- Write p = 4 * (p / 4) + 1
      set k := p / 4 with hk_def
      have hp_eq : p = 4 * k + 1 := by omega
      have hp1_eq : p - 1 = 4 * k := by omega
      -- k ≥ 1 since p ≥ 5
      have hk_pos : k ≥ 1 := by omega
      -- 2^(4k) % 10 = 6
      have h1 : (2 ^ (4 * k)) % 10 = 6 := hcycle0 k hk_pos
      -- 2^(4k+1) % 10 = 2
      have h2 : (2 ^ (4 * k + 1)) % 10 = 2 := hcycle1 k
      -- (2^(4k+1) - 1) % 10 = 1
      have h3 : (2 ^ (4 * k + 1) - 1) % 10 = 1 := by
        have : 2 ^ (4 * k + 1) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
        omega
      -- Product: (2^(4k) * (2^(4k+1) - 1)) % 10 = (6 * 1) % 10 = 6
      rw [hp1_eq, hp_eq]
      calc (2 ^ (4 * k) * (2 ^ (4 * k + 1) - 1)) % 10
          = ((2 ^ (4 * k)) % 10 * ((2 ^ (4 * k + 1) - 1) % 10)) % 10 := by rw [Nat.mul_mod]
        _ = (6 * 1) % 10 := by rw [h1, h3]
        _ = 6 := by norm_num
    · -- p % 4 = 3: product ends in 8
      right
      -- Write p = 4 * (p / 4) + 3
      set k := p / 4 with hk_def
      have hp_eq : p = 4 * k + 3 := by omega
      have hp1_eq : p - 1 = 4 * k + 2 := by omega
      have hk_pos : k ≥ 0 := by omega
      -- 2^(4k+2) % 10 = 4
      have h1 : (2 ^ (4 * k + 2)) % 10 = 4 := hcycle2 k
      -- 2^(4k+3) % 10 = 8
      have h2 : (2 ^ (4 * k + 3)) % 10 = 8 := hcycle3 k
      -- (2^(4k+3) - 1) % 10 = 7
      have h3 : (2 ^ (4 * k + 3) - 1) % 10 = 7 := by
        have : 2 ^ (4 * k + 3) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
        omega
      -- Product: (2^(4k+2) * (2^(4k+3) - 1)) % 10 = (4 * 7) % 10 = 8
      rw [hp1_eq, hp_eq]
      calc (2 ^ (4 * k + 2) * (2 ^ (4 * k + 3) - 1)) % 10
          = ((2 ^ (4 * k + 2)) % 10 * ((2 ^ (4 * k + 3) - 1) % 10)) % 10 := by rw [Nat.mul_mod]
        _ = (4 * 7) % 10 := by rw [h1, h3]
        _ = 8 := by norm_num

/-- Every even perfect number ends in 6 or 8 (its last decimal digit is 6 or 8). -/
theorem even_perfect_last_digit {n : ℕ} (he : Even n) (hp : Nat.Perfect n) :
    n % 10 = 6 ∨ n % 10 = 8 := by
  obtain ⟨p, hprime, rfl⟩ := even_perfect_classification he hp
  exact euclidEuler_form_last_digit hprime

end Brockian.EvenPerfectLastDigit

