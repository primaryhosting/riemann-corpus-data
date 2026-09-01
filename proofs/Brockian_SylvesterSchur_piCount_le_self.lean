import Mathlib
namespace Brockian.SylvesterSchur

/-!
# The Sylvester–Schur theorem

If `n > k ≥ 1` then one of `n+1, …, n+k` has a prime factor `> k`.

The proof follows Erdős' argument: assuming the contrary, every prime factor of the
binomial coefficient `(n+k).choose k` is at most `k`.  This yields two upper bounds for
that binomial coefficient (one via the number of primes `≤ k`, one via the primorial),
both of which are contradicted by an elementary lower bound, except in a range of small
parameters which is covered by an explicit chain of primes.
-/

open Finset Real

/-! ### An elementary upper bound for the prime counting function -/

/-- The number of primes `≤ k`. -/
def piCount (k : ℕ) : ℕ := #{p ∈ Finset.range (k + 1) | p.Prime}

theorem piCount_le_self (k : ℕ) : piCount k ≤ k := by
  have h : #{p ∈ Finset.range (k + 1) | p.Prime} ≤ #(Finset.Icc 2 k) := by
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact Finset.mem_Icc.2 ⟨hp.2.two_le, by omega⟩
  have h2 : #(Finset.Icc 2 k) = k - 1 := by rw [Nat.card_Icc]; omega
  unfold piCount
  omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000 in
/-- Every prime is `2`, `3`, or coprime to `6`, and among any six consecutive integers
at most two are coprime to `6`. -/
theorem three_mul_piCount_le (k : ℕ) : 3 * piCount k ≤ k + 9 := by
  by_cases hk : k ≤ 27
  · interval_cases k <;> decide
  · -- For k > 27, we bound piCount by considering primes ≤ 3 and primes > 3
    -- Primes > 3 must be coprime to 6
    have h1 : piCount k = #{p ∈ Finset.range (k + 1) | p.Prime} := rfl
    let S := {p ∈ Finset.range (k + 1) | p.Prime}
    let A := {p ∈ Finset.range 4 | p.Prime}
    let B := {p ∈ Finset.Ico 4 (k + 1) | Nat.Coprime p 6}
    have hsub : S ⊆ A ∪ B := by
      intro x hx
      simp only [S, A, B, Finset.mem_union, Finset.mem_filter] at hx ⊢
      have hxrange := hx.1
      have hxprime := hx.2
      by_cases hx3 : x < 4
      · left; simp [hx3]; exact hxprime
      · right
        have hxrange' : x < k + 1 := Finset.mem_range.mp hxrange
        have hxIco : x ∈ Finset.Ico 4 (k + 1) := Finset.mem_Ico.mpr ⟨by omega, hxrange'⟩
        have hcop : x.Coprime 6 := by
          rw [Nat.Prime.coprime_iff_not_dvd hxprime]
          exact fun h => by have := Nat.le_of_dvd (by omega) h; interval_cases x <;> trivial
        exact ⟨hxIco, hcop⟩
    have hcard : #S ≤ #A + #B := le_trans (Finset.card_le_card hsub) (Finset.card_union_le A B)
    -- #A = 2 (primes 2 and 3)
    have hA : #A = 2 := by decide
    -- #B ≤ (k + 2) / 3
    have hB : #B ≤ (k + 2) / 3 := by
      -- B ⊆ {n ∈ Ico 4 (k+1) | n % 6 = 1 ∨ n % 6 = 5}
      let C := {n ∈ Finset.Ico 4 (k + 1) | n % 6 = 1 ∨ n % 6 = 5}
      have hBC : B ⊆ C := by
        intro n hn
        simp only [B, C, Finset.mem_filter] at hn ⊢
        refine ⟨hn.1, ?_⟩
        have hc := hn.2
        rw [Nat.Coprime, Nat.gcd_comm] at hc
        have hlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
        have hcases :
            n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
          omega
        rcases hcases with hm | hm | hm | hm | hm | hm <;> simp [hm]
        -- Case n % 6 = 0: then 6 | n, so gcd 6 n = 6
        · have := Nat.dvd_of_mod_eq_zero hm; rw [Nat.gcd_eq_left this] at hc; norm_num at hc
        -- Case n % 6 = 2: then 2 | n, so gcd 6 n ≥ 2
        · have h2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega : n % 2 = 0)
          exact absurd hc (by have := Nat.dvd_gcd (by norm_num : 2 ∣ 6) h2; omega)
        -- Case n % 6 = 3: then 3 | n, so gcd 6 n ≥ 3
        · have h3 : 3 ∣ n := Nat.dvd_of_mod_eq_zero (by omega : n % 3 = 0)
          exact absurd hc (by have := Nat.dvd_gcd (by norm_num : 3 ∣ 6) h3; omega)
        -- Case n % 6 = 4: then 2 | n, so gcd 6 n ≥ 2
        · have h2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega : n % 2 = 0)
          exact absurd hc (by have := Nat.dvd_gcd (by norm_num : 2 ∣ 6) h2; omega)
      -- #B ≤ #C, and #C can be bounded by counting elements with n % 6 = 1 or 5
      have hB_le_C : #B ≤ #C := Finset.card_le_card hBC
      -- C is a subset of Ico 4 (k+1), so #C ≤ k-3
      -- More precisely, #C = #{n ∈ Ico 4 (k+1) | n % 6 = 1 ∨ n % 6 = 5}
      -- We can partition by n / 6 and show there are at most 2 values per block of 6
      calc #B ≤ #C := hB_le_C
        _ = #{n ∈ Finset.Ico 4 (k + 1) | n % 6 = 1 ∨ n % 6 = 5} := rfl
        _ ≤ (k + 2) / 3 := by
          -- For any n, n % 6 ∈ {0, 1, 2, 3, 4, 5}, and exactly 2/6 = 1/3 satisfy = 1 or = 5
          -- We can bound by noting the set is contained in the image of a smaller set
          -- Define f : n ↦ (n / 3) for n with n % 6 ∈ {1, 5}
          -- f(1) = 0, f(5) = 1, f(7) = 2, f(11) = 3, f(13) = 4, ...
          -- This is injective and maps to [0, k/3]
          -- We use that n % 6 ∈ {1, 5} means n = 6q + 1 (q ≥ 1) or n = 6q + 5 (q ≥ 0)
          -- The count is floor((k-1)/6) + floor((k-5)/6) + 1 ≤ k/3
          have hbound : ∀ n, n ∈ {n ∈ Finset.Ico 4 (k + 1) | n % 6 = 1 ∨ n % 6 = 5} →
              n / 6 < (k + 2) / 3 := by
            intro n hn
            simp only [Finset.mem_filter, Finset.mem_Ico] at hn
            omega
          let s := {n ∈ Finset.Ico 4 (k + 1) | n % 6 = 1 ∨ n % 6 = 5}
          -- Map: 6q+1 → 2q, 6q+5 → 2q+1. This is injective.
          let f : ℕ → ℕ := fun n => 2 * (n / 6) + (n % 6 - 1) / 4
          have hfbound : ∀ n, n ∈ s → f n < (k + 2) / 3 := by
            intro n hn
            simp only [s, Finset.mem_filter, Finset.mem_Ico] at hn
            rcases hn.2 with hn1 | hn5 <;> simp [f] <;> omega
          have hf_inj : ∀ n m, n ∈ s → m ∈ s → f n = f m → n = m := by
            intro n m hn hm heq
            simp only [s, Finset.mem_filter, Finset.mem_Ico] at hn hm
            -- For n % 6 = 1: f n = 2*(n/6), for n % 6 = 5: f n = 2*(n/6) + 1
            rcases hn.2 with hn1 | hn5 <;> rcases hm.2 with hm1 | hm5 <;> simp [f] at heq <;> omega
          have himage : s.image f ⊆ Finset.range ((k + 2) / 3) := by
            intro x hx
            simp only [Finset.mem_image] at hx
            obtain ⟨n, hn, rfl⟩ := hx
            exact Finset.mem_range.mpr (hfbound n hn)
          have hinjOn : Set.InjOn f (s : Set ℕ) := by
            intro a ha b hb hab
            exact hf_inj a b ha hb hab
          have hcard_le : s.card ≤ (s.image f).card := by
            rw [Finset.card_image_of_injOn hinjOn]
          calc s.card ≤ (s.image f).card := hcard_le
            _ ≤ (Finset.range ((k + 2) / 3)).card := Finset.card_le_card himage
            _ = (k + 2) / 3 := Finset.card_range _
    -- Now combine: 3 * piCount k ≤ 3 * (#A + #B) ≤ 3 * (2 + (k+2)/3) ≤ k + 9
    have hfinal : 3 * piCount k ≤ k + 9 := by
      rw [h1]
      calc 3 * #S ≤ 3 * (#A + #B) := by omega
        _ = 3 * #A + 3 * #B := by ring
        _ ≤ 3 * #A + 3 * ((k + 2) / 3) := by gcongr
        _ = 3 * 2 + 3 * ((k + 2) / 3) := by rw [hA]
        _ ≤ k + 9 := by omega
    exact hfinal

/-! ### Upper bounds for the binomial coefficient -/

/-- If all prime factors of `N.choose k` are at most `k`, then `N.choose k ≤ N ^ π(k)`. -/
theorem choose_le_pow_piCount {N k : ℕ} (hN : 0 < N)
    (H : ∀ p : ℕ, p.Prime → p ∣ N.choose k → p ≤ k) :
    N.choose k ≤ N ^ piCount k := by
  by_cases h : N.choose k = 0
  · simp [h]
  · have hpos : 0 < N.choose k := Nat.pos_of_ne_zero h
    have heq : N.choose k = (Nat.factorization (N.choose k)).prod fun p e => p ^ e := by
             rw [Nat.prod_factorization_pow_eq_self hpos.ne']
    calc N.choose k = (Nat.factorization (N.choose k)).prod fun p e => p ^ e := heq
       _ ≤ ∏ _p ∈ (N.choose k).primeFactors, N := by
             apply Finset.prod_le_prod'
             intro p hp
             have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
             have hp_dvd : p ∣ N.choose k := Nat.dvd_of_mem_primeFactors hp
             have hp_le : p ≤ k := H p hp_prime hp_dvd
             -- Need to show p^e ≤ N where e = v_p(N.choose k)
             -- This follows from e ≤ log_p(N)
             have he_bound : (N.choose k).factorization p ≤ Nat.log p N :=
               Nat.factorization_choose_le_log
             calc p ^ (N.choose k).factorization p ≤ p ^ Nat.log p N :=
                     Nat.pow_le_pow_right hp_prime.one_lt.le he_bound
               _ ≤ N := Nat.pow_log_le_self p (by omega)
       _ = N ^ (N.choose k).primeFactors.card := by simp
       _ ≤ N ^ piCount k := by
             apply Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hN)).ge
             apply Finset.card_le_card
             intro p hp
             simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
             exact ⟨H p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp),
               Nat.prime_of_mem_primeFactors hp⟩

/-- A refined upper bound: primes `p` with `N < 3 * p` do not divide `N.choose k`. -/
theorem choose_le_pow_sqrt_mul_four_pow {N k : ℕ} (hk : 26 ≤ k) (hkN : 2 * k + 1 ≤ N)
    (H : ∀ p : ℕ, p.Prime → p ∣ N.choose k → p ≤ k) :
    N.choose k ≤ N ^ Nat.sqrt N * 4 ^ min k (N / 3) := by
  have hkN' : k ≤ N := by omega
  have hNpos : 0 < N := by omega
  set M := min k (N / 3) with hMdef
  set f : ℕ → ℕ := fun p => p ^ (N.choose k).factorization p with hfdef
  have hMk : M ≤ k := min_le_left _ _
  have hMN : M ≤ N := le_trans hMk hkN'
  have hvanish : ∀ x ∈ Finset.range (N + 1), x ∉ Finset.range (M + 1) → f x = 1 := by
    intro x hx hx2
    rw [Finset.mem_range, Nat.lt_succ_iff] at hx
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hx2
    by_cases hp : x.Prime
    · rcases Nat.lt_or_ge k x with hxk | hxk
      · have hz : (N.choose k).factorization x = 0 := by
          by_contra hne
          have hdvd : x ∣ N.choose k := Nat.dvd_of_factorization_pos hne
          exact absurd (H x hp hdvd) (by omega)
        simp [hfdef, hz]
      · have h3x : N < 3 * x := by omega
        have hxne2 : x ≠ 2 := by omega
        have hz := Nat.factorization_choose_of_lt_three_mul hxne2 hxk (by omega : x ≤ N - k) h3x
        simp [hfdef, hz]
    · simp [hfdef, Nat.factorization_eq_zero_of_not_prime _ hp]
  have hsub : Finset.range (M + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    simp only [Finset.mem_range] at *
    omega
  have key : N.choose k = ∏ p ∈ Finset.range (M + 1), f p := by
    rw [← Nat.prod_pow_factorization_choose N k hkN']
    exact (Finset.prod_subset hsub hvanish).symm
  set S := {p ∈ Finset.range (M + 1) | Nat.Prime p} with hSdef
  have hS : ∏ p ∈ S, f p = ∏ p ∈ Finset.range (M + 1), f p := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose! h
    simp [hfdef, Nat.factorization_eq_zero_of_not_prime _ h]
  rw [key, ← hS, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt N)]
  apply Nat.mul_le_mul
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ N)).trans ?_
    · exact Nat.pow_factorization_choose_le hNpos
    · rw [Finset.prod_const]
      refine Nat.pow_le_pow_right (by omega) ?_
      have hc : (Finset.Icc 1 (Nat.sqrt N)).card = Nat.sqrt N := by
        rw [Nat.card_Icc]; omega
      refine (Finset.card_le_card fun x hx => ?_).trans hc.le
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow M)
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (Nat.pow_le_pow_right (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
    · refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

/-! ### Lower bounds for the binomial coefficient -/

/-- The elementary bound `(N/k)^k ≤ N.choose k`. -/
theorem pow_le_pow_mul_choose {N k : ℕ} (hkN : k ≤ N) : N ^ k ≤ k ^ k * N.choose k := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  -- Key identity: N.descFactorial k = k! * N.choose k
  have hdesc : N.descFactorial k = k.factorial * N.choose k :=
    Nat.descFactorial_eq_factorial_mul_choose N k
  -- Also: N.descFactorial k = ∏_{i ∈ range k} (N - i)
  have hprod : N.descFactorial k = ∏ i ∈ range k, (N - i) := Nat.descFactorial_eq_prod_range N k
  -- Key: N.choose k = ∏_{i=0}^{k-1} (N-i)/(k-i) ≥ (N/k)^k
  -- So N^k ≤ k^k * N.choose k
  -- We use: N.descFactorial k / k.descFactorial k = N.choose k
  have hdesc_desc : N.descFactorial k / k.descFactorial k = N.choose k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose N k,
      Nat.descFactorial_eq_factorial_mul_choose k k]
    simp only [Nat.choose_self, mul_one]
    exact Nat.mul_div_cancel_left _ (Nat.factorial_pos k)
  -- Key lemma: (N/k)^k ≤ N.descFactorial k / k.descFactorial k = N.choose k
  -- This is because ∏_{i=0}^{k-1} (N-i)/(k-i) ≥ (N/k)^k
  -- Equivalently: N^k * k.descFactorial k ≤ k^k * N.descFactorial k
  have key : N ^ k * k.descFactorial k ≤ k ^ k * N.descFactorial k := by
    -- Rewrite using products
    rw [hprod, Nat.descFactorial_eq_prod_range k k]
    -- Need: N^k * ∏_{i<k} (k-i) ≤ k^k * ∏_{i<k} (N-i)
    -- Convert N^k and k^k to products
    have hNk : N ^ k = ∏ _ ∈ Finset.range k, N := by rw [Finset.prod_const]; simp
    have hk : k ^ k = ∏ _ ∈ Finset.range k, k := by rw [Finset.prod_const]; simp
    rw [hNk, hk]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro i hi
    have hi_lt : i < k := Finset.mem_range.mp hi
    have hNi : i ≤ N := by omega
    have hki : i ≤ k := by omega
    have : N * (k - i) ≤ k * (N - i) := by
      have := Nat.mul_sub_right_distrib N i k
      have := Nat.mul_sub_right_distrib k i N
      nlinarith [Nat.sub_add_cancel hNi, Nat.sub_add_cancel hki]
    exact this
  have hdesc_pos : 0 < k.descFactorial k :=
    (Nat.descFactorial_pos (n := k) (k := k)).mpr (le_refl k)
  have hdiv : k.descFactorial k ∣ N.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose k k,
      Nat.descFactorial_eq_factorial_mul_choose N k]
    simp [Nat.choose_self]
  have h := Nat.le_div_iff_mul_le hdesc_pos |>.mpr key
  rw [Nat.mul_div_assoc _ hdiv] at h
  rwa [hdesc_desc] at h

/-- Comparison with the central binomial coefficient. -/
theorem centralBinom_mul_pow_le {N k : ℕ} (hkN : 2 * k ≤ N) :
    Nat.centralBinom k * N ^ k ≤ (2 * k) ^ k * N.choose k := by
  have key : (2 * k).descFactorial k * N ^ k ≤ (2 * k) ^ k * N.descFactorial k := by
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
    have hNk : N ^ k = ∏ _ ∈ Finset.range k, N := by rw [Finset.prod_const]; simp
    have h2k : (2 * k) ^ k = ∏ _ ∈ Finset.range k, (2 * k) := by rw [Finset.prod_const]; simp
    rw [hNk, h2k, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro i hi
    have hi_lt : i < k := Finset.mem_range.mp hi
    have h1 : i ≤ 2 * k := by omega
    have h2 : i ≤ N := by omega
    nlinarith [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  have e1 : (2 * k).descFactorial k = k.factorial * Nat.centralBinom k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    rfl
  have e2 : N.descFactorial k = k.factorial * N.choose k :=
    Nat.descFactorial_eq_factorial_mul_choose N k
  rw [e1, e2] at key
  have key2 : k.factorial * (Nat.centralBinom k * N ^ k)
      ≤ k.factorial * ((2 * k) ^ k * N.choose k) := by
    calc k.factorial * (Nat.centralBinom k * N ^ k)
        = k.factorial * Nat.centralBinom k * N ^ k := by ring
      _ ≤ (2 * k) ^ k * (k.factorial * N.choose k) := key
      _ = k.factorial * ((2 * k) ^ k * N.choose k) := by ring
  exact Nat.le_of_mul_le_mul_left key2 (Nat.factorial_pos k)

/-- The main lower bound. -/
theorem four_pow_mul_pow_lt {N k : ℕ} (hk : 4 ≤ k) (hkN : 2 * k ≤ N) :
    4 ^ k * N ^ k < k * ((2 * k) ^ k * N.choose k) := by
  have h1 : 4 ^ k < k * Nat.centralBinom k := Nat.four_pow_lt_mul_centralBinom k hk
  have h2 := centralBinom_mul_pow_le hkN
  calc 4 ^ k * N ^ k < (k * Nat.centralBinom k) * N ^ k :=
        mul_lt_mul_of_pos_right h1 (Nat.pow_pos (by omega))
    _ = k * (Nat.centralBinom k * N ^ k) := by ring
    _ ≤ k * ((2 * k) ^ k * N.choose k) := Nat.mul_le_mul_left _ h2

/-! ### The first case: `N` large compared to `k` -/

theorem pow_eleven_lt_four_pow {k : ℕ} (hk : 26 ≤ k) : k ^ 11 < 4 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 26 with h | h
    · have he : n + 1 = 26 := by omega
      rw [he]; norm_num
    · have ihn := ih (by omega)
      have step : (n + 1) ^ 11 ≤ 4 * n ^ 11 := by
        have h1 : 26 * (n + 1) ≤ 27 * n := by omega
        have h2 : (26 * (n + 1)) ^ 11 ≤ (27 * n) ^ 11 := Nat.pow_le_pow_left h1 11
        rw [mul_pow, mul_pow] at h2
        have h3 : (27 : ℕ) ^ 11 * n ^ 11 ≤ (4 * 26 ^ 11) * n ^ 11 :=
          Nat.mul_le_mul_right _ (by norm_num)
        have h4 : (26 : ℕ) ^ 11 * (n + 1) ^ 11 ≤ 26 ^ 11 * (4 * n ^ 11) := by
          calc (26 : ℕ) ^ 11 * (n + 1) ^ 11 ≤ 27 ^ 11 * n ^ 11 := h2
            _ ≤ (4 * 26 ^ 11) * n ^ 11 := h3
            _ = 26 ^ 11 * (4 * n ^ 11) := by ring
        exact Nat.le_of_mul_le_mul_left h4 (by positivity)
      calc (n + 1) ^ 11 ≤ 4 * n ^ 11 := step
        _ < 4 * 4 ^ n := by omega
        _ = 4 ^ (n + 1) := by ring

theorem caseA {N k q : ℕ} (hk : 26 ≤ k) (h : k ^ 3 ≤ N ^ 2) (hq : 3 * q ≤ k + 9) :
    k ^ (k + 1) < 2 ^ k * N ^ (k - q) := by
  set d := k - q with hddef
  have hd : 2 * k ≤ 3 * d + 9 := by omega
  have hk1 : 1 ≤ k := by omega
  obtain ⟨j, hj⟩ : ∃ j, 2 * k = j + 9 := ⟨2 * k - 9, by omega⟩
  have h1 : (k ^ 3) ^ d ≤ (N ^ 2) ^ d := Nat.pow_le_pow_left h d
  have h2 : k ^ j ≤ k ^ (3 * d) := Nat.pow_le_pow_right hk1 (by omega)
  have h3 : k ^ 11 < 4 ^ k := pow_eleven_lt_four_pow hk
  have hkey : (k ^ (k + 1)) ^ 2 < (2 ^ k * N ^ d) ^ 2 := by
    have e1 : (k ^ (k + 1)) ^ 2 = k ^ 11 * k ^ j := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have e2 : (2 ^ k * N ^ d) ^ 2 = 4 ^ k * (N ^ 2) ^ d := by
      rw [mul_pow, ← pow_mul, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      ring_nf
    rw [e1, e2]
    calc k ^ 11 * k ^ j < 4 ^ k * k ^ j :=
          mul_lt_mul_of_pos_right h3 (Nat.pow_pos (by omega))
      _ ≤ 4 ^ k * (N ^ 2) ^ d := by
          have hle : k ^ j ≤ (N ^ 2) ^ d := by
            calc k ^ j ≤ k ^ (3 * d) := h2
              _ = (k ^ 3) ^ d := by rw [← pow_mul]
              _ ≤ (N ^ 2) ^ d := h1
          exact Nat.mul_le_mul_left _ hle
  exact lt_of_pow_lt_pow_left' 2 hkey

/-! ### The second case: `N` comparable to `k` -/

/-! ### Elementary bounds on the logarithm -/

theorem one_sub_inv_le_log {z : ℝ} (hz : 0 < z) : 1 - 1 / z ≤ Real.log z := by
  have h := Real.log_le_sub_one_of_pos (x := 1 / z) (by positivity)
  rw [Real.log_div one_ne_zero hz.ne', Real.log_one] at h
  linarith

/-- A convenient upper bound: `log (v ^ 4) ≤ 7.1 + v / 4`. -/
theorem log_pow4_le {v : ℝ} (hv : 0 < v) : Real.log (v ^ 4) ≤ 7.1 + v / 4 := by
  have h16 : Real.log (v / 16) ≤ v / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hl : Real.log v = Real.log (v / 16) + Real.log 16 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; ring_nf
  have h2 : Real.log 16 ≤ 2.7725888 := by
    have h16' : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  rw [Real.log_pow]
  push_cast
  linarith

theorem nine_le_log {x : ℝ} (hx : 20000 ≤ x) : 9 ≤ Real.log x := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h : Real.exp 9 ≤ 20000 := by
    have he : Real.exp 9 = (Real.exp 1) ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    have h2 : (Real.exp 1) ^ 9 ≤ (2.7182818286 : ℝ) ^ 9 := by gcongr
    linarith [h2, show (2.7182818286 : ℝ) ^ 9 ≤ 20000 by norm_num]
  have h3 := Real.log_le_log (Real.exp_pos 9) (le_trans h hx)
  rwa [Real.log_exp] at h3

theorem log_two_le : Real.log 2 ≤ 0.6931472 := by linarith [Real.log_two_lt_d9]

theorem log_two_ge : (0.6931471 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]

theorem log_three_ge : (1.026 : ℝ) ≤ Real.log 3 := by
  have he : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h32 : (1 : ℝ) - 1 / (3 / 2) ≤ Real.log (3 / 2) := one_sub_inv_le_log (by norm_num)
  rw [he]; norm_num at h32 ⊢; linarith [log_two_ge]

theorem log_seven_thirds_ge : (0.836 : ℝ) ≤ Real.log (7 / 3) := by
  have he : Real.log (7 / 3) = Real.log 2 + Real.log (7 / 6) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h76 : (1 : ℝ) - 1 / (7 / 6) ≤ Real.log (7 / 6) := one_sub_inv_le_log (by norm_num)
  rw [he]; norm_num at h76 ⊢; linarith [log_two_ge]

theorem log_eight_thirds_ge : (0.943 : ℝ) ≤ Real.log (8 / 3) := by
  have he : Real.log (8 / 3) = Real.log 2 + Real.log (4 / 3) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h43 : (1 : ℝ) - 1 / (4 / 3) ≤ Real.log (4 / 3) := one_sub_inv_le_log (by norm_num)
  rw [he]; norm_num at h43 ⊢; linarith [log_two_ge]

theorem log_nine_ge : (2.19 : ℝ) ≤ Real.log 9 := by
  have he : Real.log 9 = 3 * Real.log 2 + Real.log (9 / 8) := by
    rw [show (3 : ℝ) * Real.log 2 = Real.log 8 by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring]
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h98 : (1 : ℝ) - 1 / (9 / 8) ≤ Real.log (9 / 8) := one_sub_inv_le_log (by norm_num)
  rw [he]; norm_num at h98 ⊢; linarith [log_two_ge]

theorem log_nine_le : Real.log 9 ≤ 2.7725888 := by
  have h4 : Real.log 9 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
  have h5 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  linarith [log_two_le]

/-! ### Polynomial estimates -/

theorem polyP1 {v w : ℝ} (hv : 11.8 ≤ v) (hw0 : 0 ≤ w) (hw2 : w ^ 2 ≤ 3 * v ^ 4) :
    (7.1 + v / 4) + w * (8.5 + v / 4) ≤ 0.23 * v ^ 4 := by
  have hv0 : (0 : ℝ) < v := by linarith
  have hvs : (0 : ℝ) ≤ v - 11.8 := by linarith
  have hw : w ≤ 1.74 * v ^ 2 := by nlinarith [sq_nonneg (w - 1.74 * v ^ 2)]
  have e1 : 0 ≤ (v - 11.8) * v ^ 3 := mul_nonneg hvs (by positivity)
  have e2 : 0 ≤ (v - 11.8) * v ^ 2 := mul_nonneg hvs (by positivity)
  have e3 : 0 ≤ (v - 11.8) * v := mul_nonneg hvs (by positivity)
  nlinarith [e1, e2, e3, hw, hv0, sq_nonneg v]

theorem polyP2 {v w : ℝ} (hv : 11.8 ≤ v) (hw2 : w ^ 2 ≤ 9 * v ^ 4) :
    (7.1 + v / 4) + w * (9.9 + v / 4) ≤ 0.3 * v ^ 4 := by
  have hv0 : (0 : ℝ) < v := by linarith
  have hvs : (0 : ℝ) ≤ v - 11.8 := by linarith
  have hw : w ≤ 3 * v ^ 2 := by nlinarith [sq_nonneg (w - 3 * v ^ 2)]
  have e1 : 0 ≤ (v - 11.8) * v ^ 3 := mul_nonneg hvs (by positivity)
  have e2 : 0 ≤ (v - 11.8) * v ^ 2 := mul_nonneg hvs (by positivity)
  have e3 : 0 ≤ (v - 11.8) * v := mul_nonneg hvs (by positivity)
  nlinarith [e1, e2, e3, hw, hv0, sq_nonneg v]

theorem polyP34 {v w : ℝ} (hv : 11.8 ≤ v) (hw2 : w ^ 2 ≤ v ^ 6) :
    (7.1 + v / 4) + w * (10.65 + 0.375 * v) ≤ 1.45 * v ^ 4 := by
  have hv0 : (0 : ℝ) < v := by linarith
  have hvs : (0 : ℝ) ≤ v - 11.8 := by linarith
  have hw : w ≤ v ^ 3 := by
    by_contra hc
    rw [not_le] at hc
    have h3 : (0 : ℝ) < v ^ 3 := by positivity
    nlinarith [hc, h3]
  have e1 : 0 ≤ (v - 11.8) * v ^ 3 := mul_nonneg hvs (by positivity)
  have e2 : 0 ≤ (v - 11.8) * v ^ 2 := mul_nonneg hvs (by positivity)
  have e3 : 0 ≤ (v - 11.8) * v := mul_nonneg hvs (by positivity)
  nlinarith [e1, e2, e3, hw, hv0, sq_nonneg v]

/-! ### The analytic heart of the second case -/

set_option maxHeartbeats 1000000 in
theorem caseB_real {x y s m : ℝ} (hx : 20000 ≤ x) (hy : 2 * x + 1 ≤ y) (hy2 : y ^ 2 ≤ x ^ 3)
    (hs : s ^ 2 ≤ y) (hm0 : 0 ≤ m) (hm1 : m ≤ x) (hm3 : 3 * m ≤ y) :
    Real.log x + x * Real.log (2 * x) + s * Real.log y + m * Real.log 4
      ≤ x * Real.log 4 + x * Real.log y := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  -- the fourth root of `x`
  obtain ⟨v, hv0, hv4⟩ : ∃ v : ℝ, 0 < v ∧ v ^ 4 = x := by
    refine ⟨Real.sqrt (Real.sqrt x), Real.sqrt_pos.2 (Real.sqrt_pos.2 hx0), ?_⟩
    have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have h2 : (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg x)
    calc (Real.sqrt (Real.sqrt x)) ^ 4 = ((Real.sqrt (Real.sqrt x)) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt x) ^ 2 := by rw [h2]
      _ = x := h1
  have hv : 11.8 ≤ v := by
    by_contra hc
    rw [not_le] at hc
    have h4 : v ^ 4 < (11.8 : ℝ) ^ 4 := by gcongr
    rw [hv4] at h4
    norm_num at h4
    linarith
  -- the square root of `y`
  obtain ⟨w, hw0, hw2⟩ : ∃ w : ℝ, 0 ≤ w ∧ w ^ 2 = y :=
    ⟨Real.sqrt y, Real.sqrt_nonneg y, Real.sq_sqrt hy0.le⟩
  have hsw : s ≤ w := by nlinarith [hs, hw0, hw2]
  -- logarithm bounds
  have hlogx_up : Real.log x ≤ 7.1 + v / 4 := by rw [← hv4]; exact log_pow4_le hv0
  have hlogx_lo : (9 : ℝ) ≤ Real.log x := nine_le_log hx
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlog4 : m * Real.log 4 ≤ 1.3863 * m := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have h2 : Real.log 4 ≤ 1.3863 := by rw [h]; linarith [log_two_le]
    calc m * Real.log 4 ≤ m * 1.3863 := mul_le_mul_of_nonneg_left h2 hm0
      _ = 1.3863 * m := by ring
  have hlog2x : Real.log (2 * x) = Real.log 2 + Real.log x :=
    Real.log_mul two_ne_zero hx0.ne'
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  -- it suffices to prove the following inequality
  have key : Real.log x + s * Real.log y + m * Real.log 4
      ≤ x * (Real.log 2 + Real.log y - Real.log x) := by
    have hsy : s * Real.log y ≤ w * Real.log y := mul_le_mul_of_nonneg_right hsw hlogy0
    rcases le_or_gt y (3 * x) with hcase | hcase
    · -- `y ≤ 3 * x`, use `m ≤ y / 3`
      have hlogy_up : Real.log y ≤ 8.5 + v / 4 := by
        have h1 : Real.log y ≤ Real.log (3 * x) := Real.log_le_log hy0 hcase
        have h2 : Real.log (3 * x) = Real.log 3 + Real.log x :=
          Real.log_mul (by norm_num) hx0.ne'
        have h3 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        linarith [log_two_le]
      have hwy : w * Real.log y ≤ w * (8.5 + v / 4) := mul_le_mul_of_nonneg_left hlogy_up hw0
      have hpoly := polyP1 hv hw0 (by rw [hw2, hv4]; linarith)
      rw [hv4] at hpoly
      have hL : Real.log x + s * Real.log y + m * Real.log 4 ≤ 0.23 * x + 1.3863 * m := by
        linarith
      -- lower bound for the right-hand side
      rcases le_or_gt (3 * y) (7 * x) with hc1 | hc1
      · have hd : (1.3862471 : ℝ) ≤ Real.log 2 + Real.log y - Real.log x := by
          have h1 : Real.log (2 * x) ≤ Real.log y := Real.log_le_log (by linarith) (by linarith)
          rw [hlog2x] at h1
          linarith [log_two_ge]
        have hR : x * 1.3862471 ≤ x * (Real.log 2 + Real.log y - Real.log x) :=
          mul_le_mul_of_nonneg_left hd hx0.le
        have hmx : 1.3863 * m ≤ 1.3863 * (7 * x / 9) := by
          have : m ≤ 7 * x / 9 := by linarith
          linarith
        linarith
      · rcases le_or_gt (3 * y) (8 * x) with hc2 | hc2
        · have hd : (1.5291471 : ℝ) ≤ Real.log 2 + Real.log y - Real.log x := by
            have h1 : Real.log (7 / 3 * x) ≤ Real.log y :=
              Real.log_le_log (by positivity) (by linarith)
            rw [Real.log_mul (by norm_num) hx0.ne'] at h1
            linarith [log_two_ge, log_seven_thirds_ge]
          have hR : x * 1.5291471 ≤ x * (Real.log 2 + Real.log y - Real.log x) :=
            mul_le_mul_of_nonneg_left hd hx0.le
          have hmx : 1.3863 * m ≤ 1.3863 * (8 * x / 9) := by
            have : m ≤ 8 * x / 9 := by linarith
            linarith
          linarith
        · have hd : (1.6361471 : ℝ) ≤ Real.log 2 + Real.log y - Real.log x := by
            have h1 : Real.log (8 / 3 * x) ≤ Real.log y :=
              Real.log_le_log (by positivity) (by linarith)
            rw [Real.log_mul (by norm_num) hx0.ne'] at h1
            linarith [log_two_ge, log_eight_thirds_ge]
          have hR : x * 1.6361471 ≤ x * (Real.log 2 + Real.log y - Real.log x) :=
            mul_le_mul_of_nonneg_left hd hx0.le
          have hmx : 1.3863 * m ≤ 1.3863 * x := by
            have : m ≤ x := by linarith
            linarith
          linarith
    · rcases le_or_gt y (9 * x) with hcase2 | hcase2
      · -- `3 * x ≤ y ≤ 9 * x`, use `m ≤ x`
        have hlogy_up : Real.log y ≤ 9.9 + v / 4 := by
          have h1 : Real.log y ≤ Real.log (9 * x) := Real.log_le_log hy0 hcase2
          have h2 : Real.log (9 * x) = Real.log 9 + Real.log x :=
            Real.log_mul (by norm_num) hx0.ne'
          linarith [log_nine_le]
        have hwy : w * Real.log y ≤ w * (9.9 + v / 4) := mul_le_mul_of_nonneg_left hlogy_up hw0
        have hpoly := polyP2 hv (by rw [hw2, hv4]; linarith)
        rw [hv4] at hpoly
        have hL : Real.log x + s * Real.log y + m * Real.log 4 ≤ 0.3 * x + 1.3863 * m := by
          linarith
        have hd : (1.7191471 : ℝ) ≤ Real.log 2 + Real.log y - Real.log x := by
          have h1 : Real.log (3 * x) ≤ Real.log y := Real.log_le_log (by positivity) (by linarith)
          rw [Real.log_mul (by norm_num) hx0.ne'] at h1
          linarith [log_two_ge, log_three_ge]
        have hR : x * 1.7191471 ≤ x * (Real.log 2 + Real.log y - Real.log x) :=
          mul_le_mul_of_nonneg_left hd hx0.le
        have hmx : 1.3863 * m ≤ 1.3863 * x := by linarith
        linarith
      · -- `9 * x ≤ y`, use `m ≤ x`
        have hlogy_up : Real.log y ≤ 10.65 + 0.375 * v := by
          have h1 : 2 * Real.log y ≤ 3 * Real.log x := by
            have h2 : Real.log (y ^ 2) ≤ Real.log (x ^ 3) := Real.log_le_log (by positivity) hy2
            rw [Real.log_pow, Real.log_pow] at h2; push_cast at h2; linarith
          linarith
        have hwy : w * Real.log y ≤ w * (10.65 + 0.375 * v) :=
          mul_le_mul_of_nonneg_left hlogy_up hw0
        have hwb : w ^ 2 ≤ v ^ 6 := by
          have h1 : (w ^ 2) ^ 2 ≤ (v ^ 6) ^ 2 := by
            rw [hw2, show (v ^ 6) ^ 2 = (v ^ 4) ^ 3 by ring, hv4]; exact hy2
          have h2 : (0 : ℝ) < v ^ 6 := by positivity
          nlinarith [h1, h2, sq_nonneg w, hw2, hy0]
        have hpoly := polyP34 hv hwb
        rw [hv4] at hpoly
        have hL : Real.log x + s * Real.log y + m * Real.log 4 ≤ 1.45 * x + 1.3863 * m := by
          linarith
        have hd : (2.8831471 : ℝ) ≤ Real.log 2 + Real.log y - Real.log x := by
          have h1 : Real.log (9 * x) ≤ Real.log y := Real.log_le_log (by positivity) (by linarith)
          rw [Real.log_mul (by norm_num) hx0.ne'] at h1
          linarith [log_two_ge, log_nine_ge]
        have hR : x * 2.8831471 ≤ x * (Real.log 2 + Real.log y - Real.log x) :=
          mul_le_mul_of_nonneg_left hd hx0.le
        have hmx : 1.3863 * m ≤ 1.3863 * x := by linarith
        linarith
  rw [hlog2x, hlog4eq]
  have expand : x * (Real.log 2 + Real.log y - Real.log x)
      = x * Real.log 2 + x * Real.log y - x * Real.log x := by ring
  rw [expand] at key
  rw [hlog4eq] at key
  linarith

theorem caseB {N k : ℕ} (hk : 20000 ≤ k) (h1 : 2 * k + 1 ≤ N) (h2 : N ^ 2 < k ^ 3) :
    k * ((2 * k) ^ k * (N ^ Nat.sqrt N * 4 ^ min k (N / 3))) ≤ 4 ^ k * N ^ k := by
  have hk0 : 0 < k := by omega
  have hN0 : 0 < N := by omega
  set s := Nat.sqrt N with hsdef
  set m := min k (N / 3) with hmdef
  have hkR : (20000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0R : (0 : ℝ) < (k : ℝ) := by positivity
  have hN0R : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hyR : 2 * (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h1
  have hy2R : (N : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by exact_mod_cast h2.le
  have hsR : ((s : ℝ)) ^ 2 ≤ (N : ℝ) := by
    have hle : s ^ 2 ≤ N := Nat.sqrt_le' N
    exact_mod_cast (Nat.cast_le (α := ℝ)).2 hle
  have hm1R : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast min_le_left k (N / 3)
  have hm3R : 3 * (m : ℝ) ≤ (N : ℝ) := by
    have hmm : 3 * m ≤ N := by
      have hmr : m ≤ N / 3 := min_le_right _ _
      omega
    exact_mod_cast hmm
  have key := caseB_real hkR hyR hy2R hsR (by positivity) hm1R hm3R
  have hL : (0 : ℝ) < (k : ℝ) * ((2 * (k : ℝ)) ^ k * ((N : ℝ) ^ s * 4 ^ m)) := by positivity
  have hR : (0 : ℝ) < 4 ^ k * (N : ℝ) ^ k := by positivity
  have hlogL : Real.log ((k : ℝ) * ((2 * (k : ℝ)) ^ k * ((N : ℝ) ^ s * 4 ^ m)))
      = Real.log k + k * Real.log (2 * k) + s * Real.log N + m * Real.log 4 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    ring
  have hlogR : Real.log ((4 : ℝ) ^ k * (N : ℝ) ^ k) = k * Real.log 4 + k * Real.log N := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hfin :
      (k : ℝ) * ((2 * (k : ℝ)) ^ k * ((N : ℝ) ^ s * 4 ^ m)) ≤ 4 ^ k * (N : ℝ) ^ k := by
    rw [← Real.log_le_log_iff hL hR, hlogL, hlogR]
    exact key
  have hcast :
      ((k * ((2 * k) ^ k * (N ^ s * 4 ^ m)) : ℕ) : ℝ) ≤ ((4 ^ k * N ^ k : ℕ) : ℝ) := by
    push_cast
    exact hfin
  exact_mod_cast hcast

/-! ### The third case: a chain of primes -/

/-- One step of the descent along a chain of primes. -/
theorem chain_step {n k : ℕ} (hnk : n ^ 2 < k ^ 3) (q p : ℕ) (hp : p.Prime)
    (hgap : (p - q - 1) ^ 3 ≤ q ^ 2) (H : n < q → ∃ r, r.Prime ∧ n < r ∧ r ≤ n + k) :
    n < p → ∃ r, r.Prime ∧ n < r ∧ r ≤ n + k := by
  intro hn
  rcases Nat.lt_or_ge n q with hq | hq
  · exact H hq
  · refine ⟨p, hp, hn, ?_⟩
    by_contra hc
    rw [not_le] at hc
    have hk : k ≤ p - q - 1 := by omega
    have h1 : k ^ 3 ≤ (p - q - 1) ^ 3 := Nat.pow_le_pow_left hk 3
    have h2 : q ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hq 2
    exact absurd hnk (by linarith)

set_option maxHeartbeats 1000000 in
/-- For `n` in the range covered by our chain of primes and `k ≥ n ^ (2/3)`,
the interval `(n, n+k]` contains a prime. -/
theorem exists_prime_in_Ioc {n k : ℕ} (h2 : 2 ≤ n) (hn : n < 2828300) (hnk : n ^ 2 < k ^ 3) :
    ∃ p, p.Prime ∧ n < p ∧ p ≤ n + k := by
  have H : n < 2 → ∃ r, r.Prime ∧ n < r ∧ r ≤ n + k := fun hlt => absurd hlt (by omega)
  replace H := chain_step hnk 2 3 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 3 5 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 5 7 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 7 11 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 11 13 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 13 19 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 19 23 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 23 31 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 31 41 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 41 53 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 53 67 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 67 83 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 83 103 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 103 113 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 113 137 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 137 163 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 163 193 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 193 227 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 227 263 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 263 293 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 293 337 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 337 383 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 383 433 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 433 491 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 491 547 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 547 613 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 613 683 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 683 761 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 761 839 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 839 919 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 919 1013 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1013 1109 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1109 1217 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1217 1327 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1327 1447 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1447 1571 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1571 1699 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1699 1831 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1831 1979 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1979 2137 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2137 2297 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2297 2467 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2467 2647 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2647 2837 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2837 3037 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 3037 3229 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 3229 3433 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 3433 3659 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 3659 3889 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 3889 4133 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 4133 4391 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 4391 4657 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 4657 4933 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 4933 5209 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 5209 5507 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 5507 5813 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 5813 6133 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 6133 6469 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 6469 6803 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 6803 7159 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 7159 7529 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 7529 7907 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 7907 8297 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 8297 8707 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 8707 9127 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 9127 9551 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 9551 9973 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 9973 10433 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 10433 10909 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 10909 11399 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 11399 11903 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 11903 12421 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 12421 12953 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 12953 13499 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 13499 14057 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 14057 14639 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 14639 15233 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 15233 15823 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 15823 16453 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 16453 17099 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 17099 17761 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 17761 18439 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 18439 19121 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 19121 19819 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 19819 20551 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 20551 21283 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 21283 22051 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 22051 22817 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 22817 23609 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 23609 24421 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 24421 25261 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 25261 26119 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 26119 26993 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 26993 27893 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 27893 28813 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 28813 29753 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 29753 30713 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 30713 31687 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 31687 32687 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 32687 33703 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 33703 34747 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 34747 35809 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 35809 36887 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 36887 37993 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 37993 39119 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 39119 40253 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 40253 41413 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 41413 42589 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 42589 43801 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 43801 45013 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 45013 46279 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 46279 47569 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 47569 48871 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 48871 50207 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 50207 51563 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 51563 52937 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 52937 54347 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 54347 55763 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 55763 57223 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 57223 58699 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 58699 60209 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 60209 61729 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 61729 63281 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 63281 64853 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 64853 66467 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 66467 68099 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 68099 69767 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 69767 71453 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 71453 73141 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 73141 74887 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 74887 76651 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 76651 78439 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 78439 80263 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 80263 82073 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 82073 83939 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 83939 85853 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 85853 87797 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 87797 89767 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 89767 91771 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 91771 93787 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 93787 95819 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 95819 97883 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 97883 100003 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 100003 102149 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 102149 104327 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 104327 106543 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 106543 108791 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 108791 111053 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 111053 113363 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 113363 115693 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 115693 118061 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 118061 120431 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 120431 122869 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 122869 125339 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 125339 127843 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 127843 130379 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 130379 132949 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 132949 135533 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 135533 138163 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 138163 140831 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 140831 143537 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 143537 146273 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 146273 149033 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 149033 151841 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 151841 154681 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 154681 157561 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 157561 160453 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 160453 163403 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 163403 166363 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 166363 169373 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 169373 172433 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 172433 175523 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 175523 178643 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 178643 181813 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 181813 185021 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 185021 188261 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 188261 191537 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 191537 194839 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 194839 198197 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 198197 201589 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 201589 205019 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 205019 208493 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 208493 211997 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 211997 215531 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 215531 219119 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 219119 222731 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 222731 226397 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 226397 230107 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 230107 233861 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 233861 237631 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 237631 241463 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 241463 245339 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 245339 249257 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 249257 253159 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 253159 257161 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 257161 261169 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 261169 265249 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 265249 269377 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 269377 273527 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 273527 277741 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 277741 281993 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 281993 286289 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 286289 290627 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 290627 295007 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 295007 299419 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 299419 303889 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 303889 308383 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 308383 312943 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 312943 317539 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 317539 322193 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 322193 326881 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 326881 331613 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 331613 336403 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 336403 341233 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 341233 346117 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 346117 351047 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 351047 356023 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 356023 361033 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 361033 366103 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 366103 371213 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 371213 376373 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 376373 381569 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 381569 386809 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 386809 392113 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 392113 397469 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 397469 402869 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 402869 408311 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 408311 413807 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 413807 419351 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 419351 424939 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 424939 430589 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 430589 436291 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 436291 442033 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 442033 447829 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 447829 453683 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 453683 459523 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 459523 465469 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 465469 471467 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 471467 477523 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 477523 483629 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 483629 489791 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 489791 495983 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 495983 502247 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 502247 508559 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 508559 514903 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 514903 521317 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 521317 527789 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 527789 534311 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 534311 540877 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 540877 547513 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 547513 554189 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 554189 560929 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 560929 567719 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 567719 574547 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 574547 581459 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 581459 588403 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 588403 595411 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 595411 602489 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 602489 609619 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 609619 616799 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 616799 624037 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 624037 631339 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 631339 638699 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 638699 646103 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 646103 653563 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 653563 661093 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 661093 668677 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 668677 676297 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 676297 683983 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 683983 691739 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 691739 699557 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 699557 707437 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 707437 715373 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 715373 723361 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 723361 731413 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 731413 739523 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 739523 747679 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 747679 755903 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 755903 764189 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 764189 772537 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 772537 780953 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 780953 789419 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 789419 797957 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 797957 806549 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 806549 815209 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 815209 823913 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 823913 832693 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 832693 841541 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 841541 850453 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 850453 859423 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 859423 868459 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 868459 877543 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 877543 886667 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 886667 895889 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 895889 905171 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 905171 914521 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 914521 923939 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 923939 933421 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 933421 942943 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 942943 952559 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 952559 962237 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 962237 971981 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 971981 981769 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 981769 991643 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 991643 1001587 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1001587 1011589 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1011589 1021663 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1021663 1031761 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1031761 1041961 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1041961 1052237 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1052237 1062563 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1062563 1072969 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1072969 1083449 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1083449 1093997 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1093997 1104613 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1104613 1115299 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1115299 1126043 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1126043 1136843 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1136843 1147717 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1147717 1158679 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1158679 1169687 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1169687 1180771 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1180771 1191941 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1191941 1203179 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1203179 1214489 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1214489 1225871 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1225871 1237309 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1237309 1248833 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1248833 1260419 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1260419 1272079 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1272079 1283797 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1283797 1295603 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1295603 1307483 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1307483 1319429 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1319429 1331443 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1331443 1343519 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1343519 1355693 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1355693 1367929 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1367929 1380251 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1380251 1392631 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1392631 1405099 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1405099 1417639 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1417639 1430243 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1430243 1442923 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1442923 1455683 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1455683 1468517 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1468517 1481413 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1481413 1494403 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1494403 1507469 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1507469 1520611 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1520611 1533817 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1533817 1547101 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1547101 1560473 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1560473 1573927 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1573927 1587449 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1587449 1601051 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1601051 1614733 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1614733 1628491 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1628491 1642327 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1642327 1656247 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1656247 1670213 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1670213 1684289 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1684289 1698427 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1698427 1712639 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1712639 1726951 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1726951 1741339 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1741339 1755799 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1755799 1770337 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1770337 1784963 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1784963 1799639 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1799639 1814431 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1814431 1829299 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1829299 1844257 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1844257 1859281 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1859281 1874399 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1874399 1889579 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1889579 1904849 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1904849 1920211 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1920211 1935641 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1935641 1951153 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1951153 1966697 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1966697 1982381 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1982381 1998133 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 1998133 2013989 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2013989 2029921 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2029921 2045929 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2045929 2062043 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2062043 2078243 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2078243 2094523 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2094523 2110891 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2110891 2127347 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2127347 2143877 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2143877 2160469 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2160469 2177167 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2177167 2193959 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2193959 2210837 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2210837 2227801 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2227801 2244859 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2244859 2261993 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2261993 2279161 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2279161 2296447 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2296447 2313851 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2313851 2331337 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2331337 2348911 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2348911 2366543 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2366543 2384297 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2384297 2402107 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2402107 2420017 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2420017 2438027 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2438027 2456141 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2456141 2474321 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2474321 2492603 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2492603 2510971 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2510971 2529421 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2529421 2547973 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2547973 2566601 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2566601 2585347 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2585347 2604167 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2604167 2623091 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2623091 2642111 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2642111 2661221 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2661221 2680421 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2680421 2699713 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2699713 2719081 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2719081 2738539 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2738539 2758109 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2758109 2777771 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2777771 2797523 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2797523 2817371 (by norm_num) (by norm_num) H
  replace H := chain_step hnk 2817371 2837309 (by norm_num) (by norm_num) H
  exact H (by omega)

/-! ### Small cases -/

/-- A list of primes used to certify the small cases. -/
def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199, 211, 223]

set_option maxRecDepth 4000 in
theorem smallPrimes_prime : ∀ p ∈ smallPrimes, Nat.Prime p := by decide

set_option maxRecDepth 100000 in
/-- For each pair `(k, n)` with `k < 26` and `n < 200`, an explicit witness `(i, p)`:
`p` is a prime larger than `k` dividing `n + 1 + i`, and `i < k`.  (For the irrelevant
pairs, those with `k = 0` or `n ≤ k`, the entry is `(0, 0)`.) -/
def smallTable : List ((ℕ × ℕ) × ℕ × ℕ) :=
  [
  ((0, 0), 0, 0), ((0, 1), 0, 0), ((0, 2), 0, 0), ((0, 3), 0, 0), ((0, 4), 0, 0), ((0, 5), 0, 0),
   ((0, 6), 0, 0), ((0, 7), 0, 0), ((0, 8), 0, 0), ((0, 9), 0, 0), ((0, 10), 0, 0),
   ((0, 11), 0, 0), ((0, 12), 0, 0), ((0, 13), 0, 0), ((0, 14), 0, 0), ((0, 15), 0, 0),
   ((0, 16), 0, 0), ((0, 17), 0, 0), ((0, 18), 0, 0), ((0, 19), 0, 0), ((0, 20), 0, 0),
   ((0, 21), 0, 0), ((0, 22), 0, 0), ((0, 23), 0, 0), ((0, 24), 0, 0), ((0, 25), 0, 0),
   ((0, 26), 0, 0), ((0, 27), 0, 0), ((0, 28), 0, 0), ((0, 29), 0, 0), ((0, 30), 0, 0),
   ((0, 31), 0, 0), ((0, 32), 0, 0), ((0, 33), 0, 0), ((0, 34), 0, 0), ((0, 35), 0, 0),
   ((0, 36), 0, 0), ((0, 37), 0, 0), ((0, 38), 0, 0), ((0, 39), 0, 0), ((0, 40), 0, 0),
   ((0, 41), 0, 0), ((0, 42), 0, 0), ((0, 43), 0, 0), ((0, 44), 0, 0), ((0, 45), 0, 0),
   ((0, 46), 0, 0), ((0, 47), 0, 0), ((0, 48), 0, 0), ((0, 49), 0, 0), ((0, 50), 0, 0),
   ((0, 51), 0, 0), ((0, 52), 0, 0), ((0, 53), 0, 0), ((0, 54), 0, 0), ((0, 55), 0, 0),
   ((0, 56), 0, 0), ((0, 57), 0, 0), ((0, 58), 0, 0), ((0, 59), 0, 0), ((0, 60), 0, 0),
   ((0, 61), 0, 0), ((0, 62), 0, 0), ((0, 63), 0, 0), ((0, 64), 0, 0), ((0, 65), 0, 0),
   ((0, 66), 0, 0), ((0, 67), 0, 0), ((0, 68), 0, 0), ((0, 69), 0, 0), ((0, 70), 0, 0),
   ((0, 71), 0, 0), ((0, 72), 0, 0), ((0, 73), 0, 0), ((0, 74), 0, 0), ((0, 75), 0, 0),
   ((0, 76), 0, 0), ((0, 77), 0, 0), ((0, 78), 0, 0), ((0, 79), 0, 0), ((0, 80), 0, 0),
   ((0, 81), 0, 0), ((0, 82), 0, 0), ((0, 83), 0, 0), ((0, 84), 0, 0), ((0, 85), 0, 0),
   ((0, 86), 0, 0), ((0, 87), 0, 0), ((0, 88), 0, 0), ((0, 89), 0, 0), ((0, 90), 0, 0),
   ((0, 91), 0, 0), ((0, 92), 0, 0), ((0, 93), 0, 0), ((0, 94), 0, 0), ((0, 95), 0, 0),
   ((0, 96), 0, 0), ((0, 97), 0, 0), ((0, 98), 0, 0), ((0, 99), 0, 0), ((0, 100), 0, 0),
   ((0, 101), 0, 0), ((0, 102), 0, 0), ((0, 103), 0, 0), ((0, 104), 0, 0), ((0, 105), 0, 0),
   ((0, 106), 0, 0), ((0, 107), 0, 0), ((0, 108), 0, 0), ((0, 109), 0, 0), ((0, 110), 0, 0),
   ((0, 111), 0, 0), ((0, 112), 0, 0), ((0, 113), 0, 0), ((0, 114), 0, 0), ((0, 115), 0, 0),
   ((0, 116), 0, 0), ((0, 117), 0, 0), ((0, 118), 0, 0), ((0, 119), 0, 0), ((0, 120), 0, 0),
   ((0, 121), 0, 0), ((0, 122), 0, 0), ((0, 123), 0, 0), ((0, 124), 0, 0), ((0, 125), 0, 0),
   ((0, 126), 0, 0), ((0, 127), 0, 0), ((0, 128), 0, 0), ((0, 129), 0, 0), ((0, 130), 0, 0),
   ((0, 131), 0, 0), ((0, 132), 0, 0), ((0, 133), 0, 0), ((0, 134), 0, 0), ((0, 135), 0, 0),
   ((0, 136), 0, 0), ((0, 137), 0, 0), ((0, 138), 0, 0), ((0, 139), 0, 0), ((0, 140), 0, 0),
   ((0, 141), 0, 0), ((0, 142), 0, 0), ((0, 143), 0, 0), ((0, 144), 0, 0), ((0, 145), 0, 0),
   ((0, 146), 0, 0), ((0, 147), 0, 0), ((0, 148), 0, 0), ((0, 149), 0, 0), ((0, 150), 0, 0),
   ((0, 151), 0, 0), ((0, 152), 0, 0), ((0, 153), 0, 0), ((0, 154), 0, 0), ((0, 155), 0, 0),
   ((0, 156), 0, 0), ((0, 157), 0, 0), ((0, 158), 0, 0), ((0, 159), 0, 0), ((0, 160), 0, 0),
   ((0, 161), 0, 0), ((0, 162), 0, 0), ((0, 163), 0, 0), ((0, 164), 0, 0), ((0, 165), 0, 0),
   ((0, 166), 0, 0), ((0, 167), 0, 0), ((0, 168), 0, 0), ((0, 169), 0, 0), ((0, 170), 0, 0),
   ((0, 171), 0, 0), ((0, 172), 0, 0), ((0, 173), 0, 0), ((0, 174), 0, 0), ((0, 175), 0, 0),
   ((0, 176), 0, 0), ((0, 177), 0, 0), ((0, 178), 0, 0), ((0, 179), 0, 0), ((0, 180), 0, 0),
   ((0, 181), 0, 0), ((0, 182), 0, 0), ((0, 183), 0, 0), ((0, 184), 0, 0), ((0, 185), 0, 0),
   ((0, 186), 0, 0), ((0, 187), 0, 0), ((0, 188), 0, 0), ((0, 189), 0, 0), ((0, 190), 0, 0),
   ((0, 191), 0, 0), ((0, 192), 0, 0), ((0, 193), 0, 0), ((0, 194), 0, 0), ((0, 195), 0, 0),
   ((0, 196), 0, 0), ((0, 197), 0, 0), ((0, 198), 0, 0), ((0, 199), 0, 0), ((1, 0), 0, 0),
   ((1, 1), 0, 0), ((1, 2), 0, 3), ((1, 3), 0, 2), ((1, 4), 0, 5), ((1, 5), 0, 3), ((1, 6), 0, 7),
   ((1, 7), 0, 2), ((1, 8), 0, 3), ((1, 9), 0, 5), ((1, 10), 0, 11), ((1, 11), 0, 3),
   ((1, 12), 0, 13), ((1, 13), 0, 7), ((1, 14), 0, 5), ((1, 15), 0, 2), ((1, 16), 0, 17),
   ((1, 17), 0, 3), ((1, 18), 0, 19), ((1, 19), 0, 5), ((1, 20), 0, 7), ((1, 21), 0, 11),
   ((1, 22), 0, 23), ((1, 23), 0, 3), ((1, 24), 0, 5), ((1, 25), 0, 13), ((1, 26), 0, 3),
   ((1, 27), 0, 7), ((1, 28), 0, 29), ((1, 29), 0, 5), ((1, 30), 0, 31), ((1, 31), 0, 2),
   ((1, 32), 0, 11), ((1, 33), 0, 17), ((1, 34), 0, 7), ((1, 35), 0, 3), ((1, 36), 0, 37),
   ((1, 37), 0, 19), ((1, 38), 0, 13), ((1, 39), 0, 5), ((1, 40), 0, 41), ((1, 41), 0, 7),
   ((1, 42), 0, 43), ((1, 43), 0, 11), ((1, 44), 0, 5), ((1, 45), 0, 23), ((1, 46), 0, 47),
   ((1, 47), 0, 3), ((1, 48), 0, 7), ((1, 49), 0, 5), ((1, 50), 0, 17), ((1, 51), 0, 13),
   ((1, 52), 0, 53), ((1, 53), 0, 3), ((1, 54), 0, 11), ((1, 55), 0, 7), ((1, 56), 0, 19),
   ((1, 57), 0, 29), ((1, 58), 0, 59), ((1, 59), 0, 5), ((1, 60), 0, 61), ((1, 61), 0, 31),
   ((1, 62), 0, 7), ((1, 63), 0, 2), ((1, 64), 0, 13), ((1, 65), 0, 11), ((1, 66), 0, 67),
   ((1, 67), 0, 17), ((1, 68), 0, 23), ((1, 69), 0, 7), ((1, 70), 0, 71), ((1, 71), 0, 3),
   ((1, 72), 0, 73), ((1, 73), 0, 37), ((1, 74), 0, 5), ((1, 75), 0, 19), ((1, 76), 0, 11),
   ((1, 77), 0, 13), ((1, 78), 0, 79), ((1, 79), 0, 5), ((1, 80), 0, 3), ((1, 81), 0, 41),
   ((1, 82), 0, 83), ((1, 83), 0, 7), ((1, 84), 0, 17), ((1, 85), 0, 43), ((1, 86), 0, 29),
   ((1, 87), 0, 11), ((1, 88), 0, 89), ((1, 89), 0, 5), ((1, 90), 0, 13), ((1, 91), 0, 23),
   ((1, 92), 0, 31), ((1, 93), 0, 47), ((1, 94), 0, 19), ((1, 95), 0, 3), ((1, 96), 0, 97),
   ((1, 97), 0, 7), ((1, 98), 0, 11), ((1, 99), 0, 5), ((1, 100), 0, 101), ((1, 101), 0, 17),
   ((1, 102), 0, 103), ((1, 103), 0, 13), ((1, 104), 0, 7), ((1, 105), 0, 53), ((1, 106), 0, 107),
   ((1, 107), 0, 3), ((1, 108), 0, 109), ((1, 109), 0, 11), ((1, 110), 0, 37), ((1, 111), 0, 7),
   ((1, 112), 0, 113), ((1, 113), 0, 19), ((1, 114), 0, 23), ((1, 115), 0, 29), ((1, 116), 0, 13),
   ((1, 117), 0, 59), ((1, 118), 0, 17), ((1, 119), 0, 5), ((1, 120), 0, 11), ((1, 121), 0, 61),
   ((1, 122), 0, 41), ((1, 123), 0, 31), ((1, 124), 0, 5), ((1, 125), 0, 7), ((1, 126), 0, 127),
   ((1, 127), 0, 2), ((1, 128), 0, 43), ((1, 129), 0, 13), ((1, 130), 0, 131), ((1, 131), 0, 11),
   ((1, 132), 0, 19), ((1, 133), 0, 67), ((1, 134), 0, 5), ((1, 135), 0, 17), ((1, 136), 0, 137),
   ((1, 137), 0, 23), ((1, 138), 0, 139), ((1, 139), 0, 7), ((1, 140), 0, 47), ((1, 141), 0, 71),
   ((1, 142), 0, 13), ((1, 143), 0, 3), ((1, 144), 0, 29), ((1, 145), 0, 73), ((1, 146), 0, 7),
   ((1, 147), 0, 37), ((1, 148), 0, 149), ((1, 149), 0, 5), ((1, 150), 0, 151), ((1, 151), 0, 19),
   ((1, 152), 0, 17), ((1, 153), 0, 11), ((1, 154), 0, 31), ((1, 155), 0, 13), ((1, 156), 0, 157),
   ((1, 157), 0, 79), ((1, 158), 0, 53), ((1, 159), 0, 5), ((1, 160), 0, 23), ((1, 161), 0, 3),
   ((1, 162), 0, 163), ((1, 163), 0, 41), ((1, 164), 0, 11), ((1, 165), 0, 83),
   ((1, 166), 0, 167), ((1, 167), 0, 7), ((1, 168), 0, 13), ((1, 169), 0, 17), ((1, 170), 0, 19),
   ((1, 171), 0, 43), ((1, 172), 0, 173), ((1, 173), 0, 29), ((1, 174), 0, 7), ((1, 175), 0, 11),
   ((1, 176), 0, 59), ((1, 177), 0, 89), ((1, 178), 0, 179), ((1, 179), 0, 5), ((1, 180), 0, 181),
   ((1, 181), 0, 13), ((1, 182), 0, 61), ((1, 183), 0, 23), ((1, 184), 0, 37), ((1, 185), 0, 31),
   ((1, 186), 0, 17), ((1, 187), 0, 47), ((1, 188), 0, 7), ((1, 189), 0, 19), ((1, 190), 0, 191),
   ((1, 191), 0, 3), ((1, 192), 0, 193), ((1, 193), 0, 97), ((1, 194), 0, 13), ((1, 195), 0, 7),
   ((1, 196), 0, 197), ((1, 197), 0, 11), ((1, 198), 0, 199), ((1, 199), 0, 5), ((2, 0), 0, 0),
   ((2, 1), 0, 0), ((2, 2), 0, 0), ((2, 3), 1, 5), ((2, 4), 0, 5), ((2, 5), 0, 3), ((2, 6), 0, 7),
   ((2, 7), 1, 3), ((2, 8), 0, 3), ((2, 9), 0, 5), ((2, 10), 0, 11), ((2, 11), 0, 3),
   ((2, 12), 0, 13), ((2, 13), 0, 7), ((2, 14), 0, 5), ((2, 15), 1, 17), ((2, 16), 0, 17),
   ((2, 17), 0, 3), ((2, 18), 0, 19), ((2, 19), 0, 5), ((2, 20), 0, 7), ((2, 21), 0, 11),
   ((2, 22), 0, 23), ((2, 23), 0, 3), ((2, 24), 0, 5), ((2, 25), 0, 13), ((2, 26), 0, 3),
   ((2, 27), 0, 7), ((2, 28), 0, 29), ((2, 29), 0, 5), ((2, 30), 0, 31), ((2, 31), 1, 11),
   ((2, 32), 0, 11), ((2, 33), 0, 17), ((2, 34), 0, 7), ((2, 35), 0, 3), ((2, 36), 0, 37),
   ((2, 37), 0, 19), ((2, 38), 0, 13), ((2, 39), 0, 5), ((2, 40), 0, 41), ((2, 41), 0, 7),
   ((2, 42), 0, 43), ((2, 43), 0, 11), ((2, 44), 0, 5), ((2, 45), 0, 23), ((2, 46), 0, 47),
   ((2, 47), 0, 3), ((2, 48), 0, 7), ((2, 49), 0, 5), ((2, 50), 0, 17), ((2, 51), 0, 13),
   ((2, 52), 0, 53), ((2, 53), 0, 3), ((2, 54), 0, 11), ((2, 55), 0, 7), ((2, 56), 0, 19),
   ((2, 57), 0, 29), ((2, 58), 0, 59), ((2, 59), 0, 5), ((2, 60), 0, 61), ((2, 61), 0, 31),
   ((2, 62), 0, 7), ((2, 63), 1, 13), ((2, 64), 0, 13), ((2, 65), 0, 11), ((2, 66), 0, 67),
   ((2, 67), 0, 17), ((2, 68), 0, 23), ((2, 69), 0, 7), ((2, 70), 0, 71), ((2, 71), 0, 3),
   ((2, 72), 0, 73), ((2, 73), 0, 37), ((2, 74), 0, 5), ((2, 75), 0, 19), ((2, 76), 0, 11),
   ((2, 77), 0, 13), ((2, 78), 0, 79), ((2, 79), 0, 5), ((2, 80), 0, 3), ((2, 81), 0, 41),
   ((2, 82), 0, 83), ((2, 83), 0, 7), ((2, 84), 0, 17), ((2, 85), 0, 43), ((2, 86), 0, 29),
   ((2, 87), 0, 11), ((2, 88), 0, 89), ((2, 89), 0, 5), ((2, 90), 0, 13), ((2, 91), 0, 23),
   ((2, 92), 0, 31), ((2, 93), 0, 47), ((2, 94), 0, 19), ((2, 95), 0, 3), ((2, 96), 0, 97),
   ((2, 97), 0, 7), ((2, 98), 0, 11), ((2, 99), 0, 5), ((2, 100), 0, 101), ((2, 101), 0, 17),
   ((2, 102), 0, 103), ((2, 103), 0, 13), ((2, 104), 0, 7), ((2, 105), 0, 53), ((2, 106), 0, 107),
   ((2, 107), 0, 3), ((2, 108), 0, 109), ((2, 109), 0, 11), ((2, 110), 0, 37), ((2, 111), 0, 7),
   ((2, 112), 0, 113), ((2, 113), 0, 19), ((2, 114), 0, 23), ((2, 115), 0, 29), ((2, 116), 0, 13),
   ((2, 117), 0, 59), ((2, 118), 0, 17), ((2, 119), 0, 5), ((2, 120), 0, 11), ((2, 121), 0, 61),
   ((2, 122), 0, 41), ((2, 123), 0, 31), ((2, 124), 0, 5), ((2, 125), 0, 7), ((2, 126), 0, 127),
   ((2, 127), 1, 43), ((2, 128), 0, 43), ((2, 129), 0, 13), ((2, 130), 0, 131), ((2, 131), 0, 11),
   ((2, 132), 0, 19), ((2, 133), 0, 67), ((2, 134), 0, 5), ((2, 135), 0, 17), ((2, 136), 0, 137),
   ((2, 137), 0, 23), ((2, 138), 0, 139), ((2, 139), 0, 7), ((2, 140), 0, 47), ((2, 141), 0, 71),
   ((2, 142), 0, 13), ((2, 143), 0, 3), ((2, 144), 0, 29), ((2, 145), 0, 73), ((2, 146), 0, 7),
   ((2, 147), 0, 37), ((2, 148), 0, 149), ((2, 149), 0, 5), ((2, 150), 0, 151), ((2, 151), 0, 19),
   ((2, 152), 0, 17), ((2, 153), 0, 11), ((2, 154), 0, 31), ((2, 155), 0, 13), ((2, 156), 0, 157),
   ((2, 157), 0, 79), ((2, 158), 0, 53), ((2, 159), 0, 5), ((2, 160), 0, 23), ((2, 161), 0, 3),
   ((2, 162), 0, 163), ((2, 163), 0, 41), ((2, 164), 0, 11), ((2, 165), 0, 83),
   ((2, 166), 0, 167), ((2, 167), 0, 7), ((2, 168), 0, 13), ((2, 169), 0, 17), ((2, 170), 0, 19),
   ((2, 171), 0, 43), ((2, 172), 0, 173), ((2, 173), 0, 29), ((2, 174), 0, 7), ((2, 175), 0, 11),
   ((2, 176), 0, 59), ((2, 177), 0, 89), ((2, 178), 0, 179), ((2, 179), 0, 5), ((2, 180), 0, 181),
   ((2, 181), 0, 13), ((2, 182), 0, 61), ((2, 183), 0, 23), ((2, 184), 0, 37), ((2, 185), 0, 31),
   ((2, 186), 0, 17), ((2, 187), 0, 47), ((2, 188), 0, 7), ((2, 189), 0, 19), ((2, 190), 0, 191),
   ((2, 191), 0, 3), ((2, 192), 0, 193), ((2, 193), 0, 97), ((2, 194), 0, 13), ((2, 195), 0, 7),
   ((2, 196), 0, 197), ((2, 197), 0, 11), ((2, 198), 0, 199), ((2, 199), 0, 5), ((3, 0), 0, 0),
   ((3, 1), 0, 0), ((3, 2), 0, 0), ((3, 3), 0, 0), ((3, 4), 0, 5), ((3, 5), 1, 7), ((3, 6), 0, 7),
   ((3, 7), 2, 5), ((3, 8), 1, 5), ((3, 9), 0, 5), ((3, 10), 0, 11), ((3, 11), 1, 13),
   ((3, 12), 0, 13), ((3, 13), 0, 7), ((3, 14), 0, 5), ((3, 15), 1, 17), ((3, 16), 0, 17),
   ((3, 17), 1, 19), ((3, 18), 0, 19), ((3, 19), 0, 5), ((3, 20), 0, 7), ((3, 21), 0, 11),
   ((3, 22), 0, 23), ((3, 23), 1, 5), ((3, 24), 0, 5), ((3, 25), 0, 13), ((3, 26), 1, 7),
   ((3, 27), 0, 7), ((3, 28), 0, 29), ((3, 29), 0, 5), ((3, 30), 0, 31), ((3, 31), 1, 11),
   ((3, 32), 0, 11), ((3, 33), 0, 17), ((3, 34), 0, 7), ((3, 35), 1, 37), ((3, 36), 0, 37),
   ((3, 37), 0, 19), ((3, 38), 0, 13), ((3, 39), 0, 5), ((3, 40), 0, 41), ((3, 41), 0, 7),
   ((3, 42), 0, 43), ((3, 43), 0, 11), ((3, 44), 0, 5), ((3, 45), 0, 23), ((3, 46), 0, 47),
   ((3, 47), 1, 7), ((3, 48), 0, 7), ((3, 49), 0, 5), ((3, 50), 0, 17), ((3, 51), 0, 13),
   ((3, 52), 0, 53), ((3, 53), 1, 11), ((3, 54), 0, 11), ((3, 55), 0, 7), ((3, 56), 0, 19),
   ((3, 57), 0, 29), ((3, 58), 0, 59), ((3, 59), 0, 5), ((3, 60), 0, 61), ((3, 61), 0, 31),
   ((3, 62), 0, 7), ((3, 63), 1, 13), ((3, 64), 0, 13), ((3, 65), 0, 11), ((3, 66), 0, 67),
   ((3, 67), 0, 17), ((3, 68), 0, 23), ((3, 69), 0, 7), ((3, 70), 0, 71), ((3, 71), 1, 73),
   ((3, 72), 0, 73), ((3, 73), 0, 37), ((3, 74), 0, 5), ((3, 75), 0, 19), ((3, 76), 0, 11),
   ((3, 77), 0, 13), ((3, 78), 0, 79), ((3, 79), 0, 5), ((3, 80), 1, 41), ((3, 81), 0, 41),
   ((3, 82), 0, 83), ((3, 83), 0, 7), ((3, 84), 0, 17), ((3, 85), 0, 43), ((3, 86), 0, 29),
   ((3, 87), 0, 11), ((3, 88), 0, 89), ((3, 89), 0, 5), ((3, 90), 0, 13), ((3, 91), 0, 23),
   ((3, 92), 0, 31), ((3, 93), 0, 47), ((3, 94), 0, 19), ((3, 95), 1, 97), ((3, 96), 0, 97),
   ((3, 97), 0, 7), ((3, 98), 0, 11), ((3, 99), 0, 5), ((3, 100), 0, 101), ((3, 101), 0, 17),
   ((3, 102), 0, 103), ((3, 103), 0, 13), ((3, 104), 0, 7), ((3, 105), 0, 53), ((3, 106), 0, 107),
   ((3, 107), 1, 109), ((3, 108), 0, 109), ((3, 109), 0, 11), ((3, 110), 0, 37), ((3, 111), 0, 7),
   ((3, 112), 0, 113), ((3, 113), 0, 19), ((3, 114), 0, 23), ((3, 115), 0, 29), ((3, 116), 0, 13),
   ((3, 117), 0, 59), ((3, 118), 0, 17), ((3, 119), 0, 5), ((3, 120), 0, 11), ((3, 121), 0, 61),
   ((3, 122), 0, 41), ((3, 123), 0, 31), ((3, 124), 0, 5), ((3, 125), 0, 7), ((3, 126), 0, 127),
   ((3, 127), 1, 43), ((3, 128), 0, 43), ((3, 129), 0, 13), ((3, 130), 0, 131), ((3, 131), 0, 11),
   ((3, 132), 0, 19), ((3, 133), 0, 67), ((3, 134), 0, 5), ((3, 135), 0, 17), ((3, 136), 0, 137),
   ((3, 137), 0, 23), ((3, 138), 0, 139), ((3, 139), 0, 7), ((3, 140), 0, 47), ((3, 141), 0, 71),
   ((3, 142), 0, 13), ((3, 143), 1, 29), ((3, 144), 0, 29), ((3, 145), 0, 73), ((3, 146), 0, 7),
   ((3, 147), 0, 37), ((3, 148), 0, 149), ((3, 149), 0, 5), ((3, 150), 0, 151), ((3, 151), 0, 19),
   ((3, 152), 0, 17), ((3, 153), 0, 11), ((3, 154), 0, 31), ((3, 155), 0, 13), ((3, 156), 0, 157),
   ((3, 157), 0, 79), ((3, 158), 0, 53), ((3, 159), 0, 5), ((3, 160), 0, 23), ((3, 161), 1, 163),
   ((3, 162), 0, 163), ((3, 163), 0, 41), ((3, 164), 0, 11), ((3, 165), 0, 83),
   ((3, 166), 0, 167), ((3, 167), 0, 7), ((3, 168), 0, 13), ((3, 169), 0, 17), ((3, 170), 0, 19),
   ((3, 171), 0, 43), ((3, 172), 0, 173), ((3, 173), 0, 29), ((3, 174), 0, 7), ((3, 175), 0, 11),
   ((3, 176), 0, 59), ((3, 177), 0, 89), ((3, 178), 0, 179), ((3, 179), 0, 5), ((3, 180), 0, 181),
   ((3, 181), 0, 13), ((3, 182), 0, 61), ((3, 183), 0, 23), ((3, 184), 0, 37), ((3, 185), 0, 31),
   ((3, 186), 0, 17), ((3, 187), 0, 47), ((3, 188), 0, 7), ((3, 189), 0, 19), ((3, 190), 0, 191),
   ((3, 191), 1, 193), ((3, 192), 0, 193), ((3, 193), 0, 97), ((3, 194), 0, 13), ((3, 195), 0, 7),
   ((3, 196), 0, 197), ((3, 197), 0, 11), ((3, 198), 0, 199), ((3, 199), 0, 5), ((4, 0), 0, 0),
   ((4, 1), 0, 0), ((4, 2), 0, 0), ((4, 3), 0, 0), ((4, 4), 0, 0), ((4, 5), 1, 7), ((4, 6), 0, 7),
   ((4, 7), 2, 5), ((4, 8), 1, 5), ((4, 9), 0, 5), ((4, 10), 0, 11), ((4, 11), 1, 13),
   ((4, 12), 0, 13), ((4, 13), 0, 7), ((4, 14), 0, 5), ((4, 15), 1, 17), ((4, 16), 0, 17),
   ((4, 17), 1, 19), ((4, 18), 0, 19), ((4, 19), 0, 5), ((4, 20), 0, 7), ((4, 21), 0, 11),
   ((4, 22), 0, 23), ((4, 23), 1, 5), ((4, 24), 0, 5), ((4, 25), 0, 13), ((4, 26), 1, 7),
   ((4, 27), 0, 7), ((4, 28), 0, 29), ((4, 29), 0, 5), ((4, 30), 0, 31), ((4, 31), 1, 11),
   ((4, 32), 0, 11), ((4, 33), 0, 17), ((4, 34), 0, 7), ((4, 35), 1, 37), ((4, 36), 0, 37),
   ((4, 37), 0, 19), ((4, 38), 0, 13), ((4, 39), 0, 5), ((4, 40), 0, 41), ((4, 41), 0, 7),
   ((4, 42), 0, 43), ((4, 43), 0, 11), ((4, 44), 0, 5), ((4, 45), 0, 23), ((4, 46), 0, 47),
   ((4, 47), 1, 7), ((4, 48), 0, 7), ((4, 49), 0, 5), ((4, 50), 0, 17), ((4, 51), 0, 13),
   ((4, 52), 0, 53), ((4, 53), 1, 11), ((4, 54), 0, 11), ((4, 55), 0, 7), ((4, 56), 0, 19),
   ((4, 57), 0, 29), ((4, 58), 0, 59), ((4, 59), 0, 5), ((4, 60), 0, 61), ((4, 61), 0, 31),
   ((4, 62), 0, 7), ((4, 63), 1, 13), ((4, 64), 0, 13), ((4, 65), 0, 11), ((4, 66), 0, 67),
   ((4, 67), 0, 17), ((4, 68), 0, 23), ((4, 69), 0, 7), ((4, 70), 0, 71), ((4, 71), 1, 73),
   ((4, 72), 0, 73), ((4, 73), 0, 37), ((4, 74), 0, 5), ((4, 75), 0, 19), ((4, 76), 0, 11),
   ((4, 77), 0, 13), ((4, 78), 0, 79), ((4, 79), 0, 5), ((4, 80), 1, 41), ((4, 81), 0, 41),
   ((4, 82), 0, 83), ((4, 83), 0, 7), ((4, 84), 0, 17), ((4, 85), 0, 43), ((4, 86), 0, 29),
   ((4, 87), 0, 11), ((4, 88), 0, 89), ((4, 89), 0, 5), ((4, 90), 0, 13), ((4, 91), 0, 23),
   ((4, 92), 0, 31), ((4, 93), 0, 47), ((4, 94), 0, 19), ((4, 95), 1, 97), ((4, 96), 0, 97),
   ((4, 97), 0, 7), ((4, 98), 0, 11), ((4, 99), 0, 5), ((4, 100), 0, 101), ((4, 101), 0, 17),
   ((4, 102), 0, 103), ((4, 103), 0, 13), ((4, 104), 0, 7), ((4, 105), 0, 53), ((4, 106), 0, 107),
   ((4, 107), 1, 109), ((4, 108), 0, 109), ((4, 109), 0, 11), ((4, 110), 0, 37), ((4, 111), 0, 7),
   ((4, 112), 0, 113), ((4, 113), 0, 19), ((4, 114), 0, 23), ((4, 115), 0, 29), ((4, 116), 0, 13),
   ((4, 117), 0, 59), ((4, 118), 0, 17), ((4, 119), 0, 5), ((4, 120), 0, 11), ((4, 121), 0, 61),
   ((4, 122), 0, 41), ((4, 123), 0, 31), ((4, 124), 0, 5), ((4, 125), 0, 7), ((4, 126), 0, 127),
   ((4, 127), 1, 43), ((4, 128), 0, 43), ((4, 129), 0, 13), ((4, 130), 0, 131), ((4, 131), 0, 11),
   ((4, 132), 0, 19), ((4, 133), 0, 67), ((4, 134), 0, 5), ((4, 135), 0, 17), ((4, 136), 0, 137),
   ((4, 137), 0, 23), ((4, 138), 0, 139), ((4, 139), 0, 7), ((4, 140), 0, 47), ((4, 141), 0, 71),
   ((4, 142), 0, 13), ((4, 143), 1, 29), ((4, 144), 0, 29), ((4, 145), 0, 73), ((4, 146), 0, 7),
   ((4, 147), 0, 37), ((4, 148), 0, 149), ((4, 149), 0, 5), ((4, 150), 0, 151), ((4, 151), 0, 19),
   ((4, 152), 0, 17), ((4, 153), 0, 11), ((4, 154), 0, 31), ((4, 155), 0, 13), ((4, 156), 0, 157),
   ((4, 157), 0, 79), ((4, 158), 0, 53), ((4, 159), 0, 5), ((4, 160), 0, 23), ((4, 161), 1, 163),
   ((4, 162), 0, 163), ((4, 163), 0, 41), ((4, 164), 0, 11), ((4, 165), 0, 83),
   ((4, 166), 0, 167), ((4, 167), 0, 7), ((4, 168), 0, 13), ((4, 169), 0, 17), ((4, 170), 0, 19),
   ((4, 171), 0, 43), ((4, 172), 0, 173), ((4, 173), 0, 29), ((4, 174), 0, 7), ((4, 175), 0, 11),
   ((4, 176), 0, 59), ((4, 177), 0, 89), ((4, 178), 0, 179), ((4, 179), 0, 5), ((4, 180), 0, 181),
   ((4, 181), 0, 13), ((4, 182), 0, 61), ((4, 183), 0, 23), ((4, 184), 0, 37), ((4, 185), 0, 31),
   ((4, 186), 0, 17), ((4, 187), 0, 47), ((4, 188), 0, 7), ((4, 189), 0, 19), ((4, 190), 0, 191),
   ((4, 191), 1, 193), ((4, 192), 0, 193), ((4, 193), 0, 97), ((4, 194), 0, 13), ((4, 195), 0, 7),
   ((4, 196), 0, 197), ((4, 197), 0, 11), ((4, 198), 0, 199), ((4, 199), 0, 5), ((5, 0), 0, 0),
   ((5, 1), 0, 0), ((5, 2), 0, 0), ((5, 3), 0, 0), ((5, 4), 0, 0), ((5, 5), 0, 0), ((5, 6), 0, 7),
   ((5, 7), 3, 11), ((5, 8), 2, 11), ((5, 9), 1, 11), ((5, 10), 0, 11), ((5, 11), 1, 13),
   ((5, 12), 0, 13), ((5, 13), 0, 7), ((5, 14), 2, 17), ((5, 15), 1, 17), ((5, 16), 0, 17),
   ((5, 17), 1, 19), ((5, 18), 0, 19), ((5, 19), 1, 7), ((5, 20), 0, 7), ((5, 21), 0, 11),
   ((5, 22), 0, 23), ((5, 23), 2, 13), ((5, 24), 1, 13), ((5, 25), 0, 13), ((5, 26), 1, 7),
   ((5, 27), 0, 7), ((5, 28), 0, 29), ((5, 29), 1, 31), ((5, 30), 0, 31), ((5, 31), 1, 11),
   ((5, 32), 0, 11), ((5, 33), 0, 17), ((5, 34), 0, 7), ((5, 35), 1, 37), ((5, 36), 0, 37),
   ((5, 37), 0, 19), ((5, 38), 0, 13), ((5, 39), 1, 41), ((5, 40), 0, 41), ((5, 41), 0, 7),
   ((5, 42), 0, 43), ((5, 43), 0, 11), ((5, 44), 1, 23), ((5, 45), 0, 23), ((5, 46), 0, 47),
   ((5, 47), 1, 7), ((5, 48), 0, 7), ((5, 49), 1, 17), ((5, 50), 0, 17), ((5, 51), 0, 13),
   ((5, 52), 0, 53), ((5, 53), 1, 11), ((5, 54), 0, 11), ((5, 55), 0, 7), ((5, 56), 0, 19),
   ((5, 57), 0, 29), ((5, 58), 0, 59), ((5, 59), 1, 61), ((5, 60), 0, 61), ((5, 61), 0, 31),
   ((5, 62), 0, 7), ((5, 63), 1, 13), ((5, 64), 0, 13), ((5, 65), 0, 11), ((5, 66), 0, 67),
   ((5, 67), 0, 17), ((5, 68), 0, 23), ((5, 69), 0, 7), ((5, 70), 0, 71), ((5, 71), 1, 73),
   ((5, 72), 0, 73), ((5, 73), 0, 37), ((5, 74), 1, 19), ((5, 75), 0, 19), ((5, 76), 0, 11),
   ((5, 77), 0, 13), ((5, 78), 0, 79), ((5, 79), 2, 41), ((5, 80), 1, 41), ((5, 81), 0, 41),
   ((5, 82), 0, 83), ((5, 83), 0, 7), ((5, 84), 0, 17), ((5, 85), 0, 43), ((5, 86), 0, 29),
   ((5, 87), 0, 11), ((5, 88), 0, 89), ((5, 89), 1, 13), ((5, 90), 0, 13), ((5, 91), 0, 23),
   ((5, 92), 0, 31), ((5, 93), 0, 47), ((5, 94), 0, 19), ((5, 95), 1, 97), ((5, 96), 0, 97),
   ((5, 97), 0, 7), ((5, 98), 0, 11), ((5, 99), 1, 101), ((5, 100), 0, 101), ((5, 101), 0, 17),
   ((5, 102), 0, 103), ((5, 103), 0, 13), ((5, 104), 0, 7), ((5, 105), 0, 53), ((5, 106), 0, 107),
   ((5, 107), 1, 109), ((5, 108), 0, 109), ((5, 109), 0, 11), ((5, 110), 0, 37), ((5, 111), 0, 7),
   ((5, 112), 0, 113), ((5, 113), 0, 19), ((5, 114), 0, 23), ((5, 115), 0, 29), ((5, 116), 0, 13),
   ((5, 117), 0, 59), ((5, 118), 0, 17), ((5, 119), 1, 11), ((5, 120), 0, 11), ((5, 121), 0, 61),
   ((5, 122), 0, 41), ((5, 123), 0, 31), ((5, 124), 1, 7), ((5, 125), 0, 7), ((5, 126), 0, 127),
   ((5, 127), 1, 43), ((5, 128), 0, 43), ((5, 129), 0, 13), ((5, 130), 0, 131), ((5, 131), 0, 11),
   ((5, 132), 0, 19), ((5, 133), 0, 67), ((5, 134), 1, 17), ((5, 135), 0, 17), ((5, 136), 0, 137),
   ((5, 137), 0, 23), ((5, 138), 0, 139), ((5, 139), 0, 7), ((5, 140), 0, 47), ((5, 141), 0, 71),
   ((5, 142), 0, 13), ((5, 143), 1, 29), ((5, 144), 0, 29), ((5, 145), 0, 73), ((5, 146), 0, 7),
   ((5, 147), 0, 37), ((5, 148), 0, 149), ((5, 149), 1, 151), ((5, 150), 0, 151),
   ((5, 151), 0, 19), ((5, 152), 0, 17), ((5, 153), 0, 11), ((5, 154), 0, 31), ((5, 155), 0, 13),
   ((5, 156), 0, 157), ((5, 157), 0, 79), ((5, 158), 0, 53), ((5, 159), 1, 23), ((5, 160), 0, 23),
   ((5, 161), 1, 163), ((5, 162), 0, 163), ((5, 163), 0, 41), ((5, 164), 0, 11),
   ((5, 165), 0, 83), ((5, 166), 0, 167), ((5, 167), 0, 7), ((5, 168), 0, 13), ((5, 169), 0, 17),
   ((5, 170), 0, 19), ((5, 171), 0, 43), ((5, 172), 0, 173), ((5, 173), 0, 29), ((5, 174), 0, 7),
   ((5, 175), 0, 11), ((5, 176), 0, 59), ((5, 177), 0, 89), ((5, 178), 0, 179),
   ((5, 179), 1, 181), ((5, 180), 0, 181), ((5, 181), 0, 13), ((5, 182), 0, 61),
   ((5, 183), 0, 23), ((5, 184), 0, 37), ((5, 185), 0, 31), ((5, 186), 0, 17), ((5, 187), 0, 47),
   ((5, 188), 0, 7), ((5, 189), 0, 19), ((5, 190), 0, 191), ((5, 191), 1, 193),
   ((5, 192), 0, 193), ((5, 193), 0, 97), ((5, 194), 0, 13), ((5, 195), 0, 7), ((5, 196), 0, 197),
   ((5, 197), 0, 11), ((5, 198), 0, 199), ((5, 199), 1, 67), ((6, 0), 0, 0), ((6, 1), 0, 0),
   ((6, 2), 0, 0), ((6, 3), 0, 0), ((6, 4), 0, 0), ((6, 5), 0, 0), ((6, 6), 0, 0),
   ((6, 7), 3, 11), ((6, 8), 2, 11), ((6, 9), 1, 11), ((6, 10), 0, 11), ((6, 11), 1, 13),
   ((6, 12), 0, 13), ((6, 13), 0, 7), ((6, 14), 2, 17), ((6, 15), 1, 17), ((6, 16), 0, 17),
   ((6, 17), 1, 19), ((6, 18), 0, 19), ((6, 19), 1, 7), ((6, 20), 0, 7), ((6, 21), 0, 11),
   ((6, 22), 0, 23), ((6, 23), 2, 13), ((6, 24), 1, 13), ((6, 25), 0, 13), ((6, 26), 1, 7),
   ((6, 27), 0, 7), ((6, 28), 0, 29), ((6, 29), 1, 31), ((6, 30), 0, 31), ((6, 31), 1, 11),
   ((6, 32), 0, 11), ((6, 33), 0, 17), ((6, 34), 0, 7), ((6, 35), 1, 37), ((6, 36), 0, 37),
   ((6, 37), 0, 19), ((6, 38), 0, 13), ((6, 39), 1, 41), ((6, 40), 0, 41), ((6, 41), 0, 7),
   ((6, 42), 0, 43), ((6, 43), 0, 11), ((6, 44), 1, 23), ((6, 45), 0, 23), ((6, 46), 0, 47),
   ((6, 47), 1, 7), ((6, 48), 0, 7), ((6, 49), 1, 17), ((6, 50), 0, 17), ((6, 51), 0, 13),
   ((6, 52), 0, 53), ((6, 53), 1, 11), ((6, 54), 0, 11), ((6, 55), 0, 7), ((6, 56), 0, 19),
   ((6, 57), 0, 29), ((6, 58), 0, 59), ((6, 59), 1, 61), ((6, 60), 0, 61), ((6, 61), 0, 31),
   ((6, 62), 0, 7), ((6, 63), 1, 13), ((6, 64), 0, 13), ((6, 65), 0, 11), ((6, 66), 0, 67),
   ((6, 67), 0, 17), ((6, 68), 0, 23), ((6, 69), 0, 7), ((6, 70), 0, 71), ((6, 71), 1, 73),
   ((6, 72), 0, 73), ((6, 73), 0, 37), ((6, 74), 1, 19), ((6, 75), 0, 19), ((6, 76), 0, 11),
   ((6, 77), 0, 13), ((6, 78), 0, 79), ((6, 79), 2, 41), ((6, 80), 1, 41), ((6, 81), 0, 41),
   ((6, 82), 0, 83), ((6, 83), 0, 7), ((6, 84), 0, 17), ((6, 85), 0, 43), ((6, 86), 0, 29),
   ((6, 87), 0, 11), ((6, 88), 0, 89), ((6, 89), 1, 13), ((6, 90), 0, 13), ((6, 91), 0, 23),
   ((6, 92), 0, 31), ((6, 93), 0, 47), ((6, 94), 0, 19), ((6, 95), 1, 97), ((6, 96), 0, 97),
   ((6, 97), 0, 7), ((6, 98), 0, 11), ((6, 99), 1, 101), ((6, 100), 0, 101), ((6, 101), 0, 17),
   ((6, 102), 0, 103), ((6, 103), 0, 13), ((6, 104), 0, 7), ((6, 105), 0, 53), ((6, 106), 0, 107),
   ((6, 107), 1, 109), ((6, 108), 0, 109), ((6, 109), 0, 11), ((6, 110), 0, 37), ((6, 111), 0, 7),
   ((6, 112), 0, 113), ((6, 113), 0, 19), ((6, 114), 0, 23), ((6, 115), 0, 29), ((6, 116), 0, 13),
   ((6, 117), 0, 59), ((6, 118), 0, 17), ((6, 119), 1, 11), ((6, 120), 0, 11), ((6, 121), 0, 61),
   ((6, 122), 0, 41), ((6, 123), 0, 31), ((6, 124), 1, 7), ((6, 125), 0, 7), ((6, 126), 0, 127),
   ((6, 127), 1, 43), ((6, 128), 0, 43), ((6, 129), 0, 13), ((6, 130), 0, 131), ((6, 131), 0, 11),
   ((6, 132), 0, 19), ((6, 133), 0, 67), ((6, 134), 1, 17), ((6, 135), 0, 17), ((6, 136), 0, 137),
   ((6, 137), 0, 23), ((6, 138), 0, 139), ((6, 139), 0, 7), ((6, 140), 0, 47), ((6, 141), 0, 71),
   ((6, 142), 0, 13), ((6, 143), 1, 29), ((6, 144), 0, 29), ((6, 145), 0, 73), ((6, 146), 0, 7),
   ((6, 147), 0, 37), ((6, 148), 0, 149), ((6, 149), 1, 151), ((6, 150), 0, 151),
   ((6, 151), 0, 19), ((6, 152), 0, 17), ((6, 153), 0, 11), ((6, 154), 0, 31), ((6, 155), 0, 13),
   ((6, 156), 0, 157), ((6, 157), 0, 79), ((6, 158), 0, 53), ((6, 159), 1, 23), ((6, 160), 0, 23),
   ((6, 161), 1, 163), ((6, 162), 0, 163), ((6, 163), 0, 41), ((6, 164), 0, 11),
   ((6, 165), 0, 83), ((6, 166), 0, 167), ((6, 167), 0, 7), ((6, 168), 0, 13), ((6, 169), 0, 17),
   ((6, 170), 0, 19), ((6, 171), 0, 43), ((6, 172), 0, 173), ((6, 173), 0, 29), ((6, 174), 0, 7),
   ((6, 175), 0, 11), ((6, 176), 0, 59), ((6, 177), 0, 89), ((6, 178), 0, 179),
   ((6, 179), 1, 181), ((6, 180), 0, 181), ((6, 181), 0, 13), ((6, 182), 0, 61),
   ((6, 183), 0, 23), ((6, 184), 0, 37), ((6, 185), 0, 31), ((6, 186), 0, 17), ((6, 187), 0, 47),
   ((6, 188), 0, 7), ((6, 189), 0, 19), ((6, 190), 0, 191), ((6, 191), 1, 193),
   ((6, 192), 0, 193), ((6, 193), 0, 97), ((6, 194), 0, 13), ((6, 195), 0, 7), ((6, 196), 0, 197),
   ((6, 197), 0, 11), ((6, 198), 0, 199), ((6, 199), 1, 67), ((7, 0), 0, 0), ((7, 1), 0, 0),
   ((7, 2), 0, 0), ((7, 3), 0, 0), ((7, 4), 0, 0), ((7, 5), 0, 0), ((7, 6), 0, 0), ((7, 7), 0, 0),
   ((7, 8), 2, 11), ((7, 9), 1, 11), ((7, 10), 0, 11), ((7, 11), 1, 13), ((7, 12), 0, 13),
   ((7, 13), 3, 17), ((7, 14), 2, 17), ((7, 15), 1, 17), ((7, 16), 0, 17), ((7, 17), 1, 19),
   ((7, 18), 0, 19), ((7, 19), 2, 11), ((7, 20), 1, 11), ((7, 21), 0, 11), ((7, 22), 0, 23),
   ((7, 23), 2, 13), ((7, 24), 1, 13), ((7, 25), 0, 13), ((7, 26), 2, 29), ((7, 27), 1, 29),
   ((7, 28), 0, 29), ((7, 29), 1, 31), ((7, 30), 0, 31), ((7, 31), 1, 11), ((7, 32), 0, 11),
   ((7, 33), 0, 17), ((7, 34), 2, 37), ((7, 35), 1, 37), ((7, 36), 0, 37), ((7, 37), 0, 19),
   ((7, 38), 0, 13), ((7, 39), 1, 41), ((7, 40), 0, 41), ((7, 41), 1, 43), ((7, 42), 0, 43),
   ((7, 43), 0, 11), ((7, 44), 1, 23), ((7, 45), 0, 23), ((7, 46), 0, 47), ((7, 47), 3, 17),
   ((7, 48), 2, 17), ((7, 49), 1, 17), ((7, 50), 0, 17), ((7, 51), 0, 13), ((7, 52), 0, 53),
   ((7, 53), 1, 11), ((7, 54), 0, 11), ((7, 55), 1, 19), ((7, 56), 0, 19), ((7, 57), 0, 29),
   ((7, 58), 0, 59), ((7, 59), 1, 61), ((7, 60), 0, 61), ((7, 61), 0, 31), ((7, 62), 2, 13),
   ((7, 63), 1, 13), ((7, 64), 0, 13), ((7, 65), 0, 11), ((7, 66), 0, 67), ((7, 67), 0, 17),
   ((7, 68), 0, 23), ((7, 69), 1, 71), ((7, 70), 0, 71), ((7, 71), 1, 73), ((7, 72), 0, 73),
   ((7, 73), 0, 37), ((7, 74), 1, 19), ((7, 75), 0, 19), ((7, 76), 0, 11), ((7, 77), 0, 13),
   ((7, 78), 0, 79), ((7, 79), 2, 41), ((7, 80), 1, 41), ((7, 81), 0, 41), ((7, 82), 0, 83),
   ((7, 83), 1, 17), ((7, 84), 0, 17), ((7, 85), 0, 43), ((7, 86), 0, 29), ((7, 87), 0, 11),
   ((7, 88), 0, 89), ((7, 89), 1, 13), ((7, 90), 0, 13), ((7, 91), 0, 23), ((7, 92), 0, 31),
   ((7, 93), 0, 47), ((7, 94), 0, 19), ((7, 95), 1, 97), ((7, 96), 0, 97), ((7, 97), 1, 11),
   ((7, 98), 0, 11), ((7, 99), 1, 101), ((7, 100), 0, 101), ((7, 101), 0, 17), ((7, 102), 0, 103),
   ((7, 103), 0, 13), ((7, 104), 1, 53), ((7, 105), 0, 53), ((7, 106), 0, 107),
   ((7, 107), 1, 109), ((7, 108), 0, 109), ((7, 109), 0, 11), ((7, 110), 0, 37),
   ((7, 111), 1, 113), ((7, 112), 0, 113), ((7, 113), 0, 19), ((7, 114), 0, 23),
   ((7, 115), 0, 29), ((7, 116), 0, 13), ((7, 117), 0, 59), ((7, 118), 0, 17), ((7, 119), 1, 11),
   ((7, 120), 0, 11), ((7, 121), 0, 61), ((7, 122), 0, 41), ((7, 123), 0, 31), ((7, 124), 2, 127),
   ((7, 125), 1, 127), ((7, 126), 0, 127), ((7, 127), 1, 43), ((7, 128), 0, 43),
   ((7, 129), 0, 13), ((7, 130), 0, 131), ((7, 131), 0, 11), ((7, 132), 0, 19), ((7, 133), 0, 67),
   ((7, 134), 1, 17), ((7, 135), 0, 17), ((7, 136), 0, 137), ((7, 137), 0, 23),
   ((7, 138), 0, 139), ((7, 139), 1, 47), ((7, 140), 0, 47), ((7, 141), 0, 71), ((7, 142), 0, 13),
   ((7, 143), 1, 29), ((7, 144), 0, 29), ((7, 145), 0, 73), ((7, 146), 1, 37), ((7, 147), 0, 37),
   ((7, 148), 0, 149), ((7, 149), 1, 151), ((7, 150), 0, 151), ((7, 151), 0, 19),
   ((7, 152), 0, 17), ((7, 153), 0, 11), ((7, 154), 0, 31), ((7, 155), 0, 13), ((7, 156), 0, 157),
   ((7, 157), 0, 79), ((7, 158), 0, 53), ((7, 159), 1, 23), ((7, 160), 0, 23), ((7, 161), 1, 163),
   ((7, 162), 0, 163), ((7, 163), 0, 41), ((7, 164), 0, 11), ((7, 165), 0, 83),
   ((7, 166), 0, 167), ((7, 167), 1, 13), ((7, 168), 0, 13), ((7, 169), 0, 17), ((7, 170), 0, 19),
   ((7, 171), 0, 43), ((7, 172), 0, 173), ((7, 173), 0, 29), ((7, 174), 1, 11), ((7, 175), 0, 11),
   ((7, 176), 0, 59), ((7, 177), 0, 89), ((7, 178), 0, 179), ((7, 179), 1, 181),
   ((7, 180), 0, 181), ((7, 181), 0, 13), ((7, 182), 0, 61), ((7, 183), 0, 23), ((7, 184), 0, 37),
   ((7, 185), 0, 31), ((7, 186), 0, 17), ((7, 187), 0, 47), ((7, 188), 1, 19), ((7, 189), 0, 19),
   ((7, 190), 0, 191), ((7, 191), 1, 193), ((7, 192), 0, 193), ((7, 193), 0, 97),
   ((7, 194), 0, 13), ((7, 195), 1, 197), ((7, 196), 0, 197), ((7, 197), 0, 11),
   ((7, 198), 0, 199), ((7, 199), 1, 67), ((8, 0), 0, 0), ((8, 1), 0, 0), ((8, 2), 0, 0),
   ((8, 3), 0, 0), ((8, 4), 0, 0), ((8, 5), 0, 0), ((8, 6), 0, 0), ((8, 7), 0, 0), ((8, 8), 0, 0),
   ((8, 9), 1, 11), ((8, 10), 0, 11), ((8, 11), 1, 13), ((8, 12), 0, 13), ((8, 13), 3, 17),
   ((8, 14), 2, 17), ((8, 15), 1, 17), ((8, 16), 0, 17), ((8, 17), 1, 19), ((8, 18), 0, 19),
   ((8, 19), 2, 11), ((8, 20), 1, 11), ((8, 21), 0, 11), ((8, 22), 0, 23), ((8, 23), 2, 13),
   ((8, 24), 1, 13), ((8, 25), 0, 13), ((8, 26), 2, 29), ((8, 27), 1, 29), ((8, 28), 0, 29),
   ((8, 29), 1, 31), ((8, 30), 0, 31), ((8, 31), 1, 11), ((8, 32), 0, 11), ((8, 33), 0, 17),
   ((8, 34), 2, 37), ((8, 35), 1, 37), ((8, 36), 0, 37), ((8, 37), 0, 19), ((8, 38), 0, 13),
   ((8, 39), 1, 41), ((8, 40), 0, 41), ((8, 41), 1, 43), ((8, 42), 0, 43), ((8, 43), 0, 11),
   ((8, 44), 1, 23), ((8, 45), 0, 23), ((8, 46), 0, 47), ((8, 47), 3, 17), ((8, 48), 2, 17),
   ((8, 49), 1, 17), ((8, 50), 0, 17), ((8, 51), 0, 13), ((8, 52), 0, 53), ((8, 53), 1, 11),
   ((8, 54), 0, 11), ((8, 55), 1, 19), ((8, 56), 0, 19), ((8, 57), 0, 29), ((8, 58), 0, 59),
   ((8, 59), 1, 61), ((8, 60), 0, 61), ((8, 61), 0, 31), ((8, 62), 2, 13), ((8, 63), 1, 13),
   ((8, 64), 0, 13), ((8, 65), 0, 11), ((8, 66), 0, 67), ((8, 67), 0, 17), ((8, 68), 0, 23),
   ((8, 69), 1, 71), ((8, 70), 0, 71), ((8, 71), 1, 73), ((8, 72), 0, 73), ((8, 73), 0, 37),
   ((8, 74), 1, 19), ((8, 75), 0, 19), ((8, 76), 0, 11), ((8, 77), 0, 13), ((8, 78), 0, 79),
   ((8, 79), 2, 41), ((8, 80), 1, 41), ((8, 81), 0, 41), ((8, 82), 0, 83), ((8, 83), 1, 17),
   ((8, 84), 0, 17), ((8, 85), 0, 43), ((8, 86), 0, 29), ((8, 87), 0, 11), ((8, 88), 0, 89),
   ((8, 89), 1, 13), ((8, 90), 0, 13), ((8, 91), 0, 23), ((8, 92), 0, 31), ((8, 93), 0, 47),
   ((8, 94), 0, 19), ((8, 95), 1, 97), ((8, 96), 0, 97), ((8, 97), 1, 11), ((8, 98), 0, 11),
   ((8, 99), 1, 101), ((8, 100), 0, 101), ((8, 101), 0, 17), ((8, 102), 0, 103),
   ((8, 103), 0, 13), ((8, 104), 1, 53), ((8, 105), 0, 53), ((8, 106), 0, 107),
   ((8, 107), 1, 109), ((8, 108), 0, 109), ((8, 109), 0, 11), ((8, 110), 0, 37),
   ((8, 111), 1, 113), ((8, 112), 0, 113), ((8, 113), 0, 19), ((8, 114), 0, 23),
   ((8, 115), 0, 29), ((8, 116), 0, 13), ((8, 117), 0, 59), ((8, 118), 0, 17), ((8, 119), 1, 11),
   ((8, 120), 0, 11), ((8, 121), 0, 61), ((8, 122), 0, 41), ((8, 123), 0, 31), ((8, 124), 2, 127),
   ((8, 125), 1, 127), ((8, 126), 0, 127), ((8, 127), 1, 43), ((8, 128), 0, 43),
   ((8, 129), 0, 13), ((8, 130), 0, 131), ((8, 131), 0, 11), ((8, 132), 0, 19), ((8, 133), 0, 67),
   ((8, 134), 1, 17), ((8, 135), 0, 17), ((8, 136), 0, 137), ((8, 137), 0, 23),
   ((8, 138), 0, 139), ((8, 139), 1, 47), ((8, 140), 0, 47), ((8, 141), 0, 71), ((8, 142), 0, 13),
   ((8, 143), 1, 29), ((8, 144), 0, 29), ((8, 145), 0, 73), ((8, 146), 1, 37), ((8, 147), 0, 37),
   ((8, 148), 0, 149), ((8, 149), 1, 151), ((8, 150), 0, 151), ((8, 151), 0, 19),
   ((8, 152), 0, 17), ((8, 153), 0, 11), ((8, 154), 0, 31), ((8, 155), 0, 13), ((8, 156), 0, 157),
   ((8, 157), 0, 79), ((8, 158), 0, 53), ((8, 159), 1, 23), ((8, 160), 0, 23), ((8, 161), 1, 163),
   ((8, 162), 0, 163), ((8, 163), 0, 41), ((8, 164), 0, 11), ((8, 165), 0, 83),
   ((8, 166), 0, 167), ((8, 167), 1, 13), ((8, 168), 0, 13), ((8, 169), 0, 17), ((8, 170), 0, 19),
   ((8, 171), 0, 43), ((8, 172), 0, 173), ((8, 173), 0, 29), ((8, 174), 1, 11), ((8, 175), 0, 11),
   ((8, 176), 0, 59), ((8, 177), 0, 89), ((8, 178), 0, 179), ((8, 179), 1, 181),
   ((8, 180), 0, 181), ((8, 181), 0, 13), ((8, 182), 0, 61), ((8, 183), 0, 23), ((8, 184), 0, 37),
   ((8, 185), 0, 31), ((8, 186), 0, 17), ((8, 187), 0, 47), ((8, 188), 1, 19), ((8, 189), 0, 19),
   ((8, 190), 0, 191), ((8, 191), 1, 193), ((8, 192), 0, 193), ((8, 193), 0, 97),
   ((8, 194), 0, 13), ((8, 195), 1, 197), ((8, 196), 0, 197), ((8, 197), 0, 11),
   ((8, 198), 0, 199), ((8, 199), 1, 67), ((9, 0), 0, 0), ((9, 1), 0, 0), ((9, 2), 0, 0),
   ((9, 3), 0, 0), ((9, 4), 0, 0), ((9, 5), 0, 0), ((9, 6), 0, 0), ((9, 7), 0, 0), ((9, 8), 0, 0),
   ((9, 9), 0, 0), ((9, 10), 0, 11), ((9, 11), 1, 13), ((9, 12), 0, 13), ((9, 13), 3, 17),
   ((9, 14), 2, 17), ((9, 15), 1, 17), ((9, 16), 0, 17), ((9, 17), 1, 19), ((9, 18), 0, 19),
   ((9, 19), 2, 11), ((9, 20), 1, 11), ((9, 21), 0, 11), ((9, 22), 0, 23), ((9, 23), 2, 13),
   ((9, 24), 1, 13), ((9, 25), 0, 13), ((9, 26), 2, 29), ((9, 27), 1, 29), ((9, 28), 0, 29),
   ((9, 29), 1, 31), ((9, 30), 0, 31), ((9, 31), 1, 11), ((9, 32), 0, 11), ((9, 33), 0, 17),
   ((9, 34), 2, 37), ((9, 35), 1, 37), ((9, 36), 0, 37), ((9, 37), 0, 19), ((9, 38), 0, 13),
   ((9, 39), 1, 41), ((9, 40), 0, 41), ((9, 41), 1, 43), ((9, 42), 0, 43), ((9, 43), 0, 11),
   ((9, 44), 1, 23), ((9, 45), 0, 23), ((9, 46), 0, 47), ((9, 47), 3, 17), ((9, 48), 2, 17),
   ((9, 49), 1, 17), ((9, 50), 0, 17), ((9, 51), 0, 13), ((9, 52), 0, 53), ((9, 53), 1, 11),
   ((9, 54), 0, 11), ((9, 55), 1, 19), ((9, 56), 0, 19), ((9, 57), 0, 29), ((9, 58), 0, 59),
   ((9, 59), 1, 61), ((9, 60), 0, 61), ((9, 61), 0, 31), ((9, 62), 2, 13), ((9, 63), 1, 13),
   ((9, 64), 0, 13), ((9, 65), 0, 11), ((9, 66), 0, 67), ((9, 67), 0, 17), ((9, 68), 0, 23),
   ((9, 69), 1, 71), ((9, 70), 0, 71), ((9, 71), 1, 73), ((9, 72), 0, 73), ((9, 73), 0, 37),
   ((9, 74), 1, 19), ((9, 75), 0, 19), ((9, 76), 0, 11), ((9, 77), 0, 13), ((9, 78), 0, 79),
   ((9, 79), 2, 41), ((9, 80), 1, 41), ((9, 81), 0, 41), ((9, 82), 0, 83), ((9, 83), 1, 17),
   ((9, 84), 0, 17), ((9, 85), 0, 43), ((9, 86), 0, 29), ((9, 87), 0, 11), ((9, 88), 0, 89),
   ((9, 89), 1, 13), ((9, 90), 0, 13), ((9, 91), 0, 23), ((9, 92), 0, 31), ((9, 93), 0, 47),
   ((9, 94), 0, 19), ((9, 95), 1, 97), ((9, 96), 0, 97), ((9, 97), 1, 11), ((9, 98), 0, 11),
   ((9, 99), 1, 101), ((9, 100), 0, 101), ((9, 101), 0, 17), ((9, 102), 0, 103),
   ((9, 103), 0, 13), ((9, 104), 1, 53), ((9, 105), 0, 53), ((9, 106), 0, 107),
   ((9, 107), 1, 109), ((9, 108), 0, 109), ((9, 109), 0, 11), ((9, 110), 0, 37),
   ((9, 111), 1, 113), ((9, 112), 0, 113), ((9, 113), 0, 19), ((9, 114), 0, 23),
   ((9, 115), 0, 29), ((9, 116), 0, 13), ((9, 117), 0, 59), ((9, 118), 0, 17), ((9, 119), 1, 11),
   ((9, 120), 0, 11), ((9, 121), 0, 61), ((9, 122), 0, 41), ((9, 123), 0, 31), ((9, 124), 2, 127),
   ((9, 125), 1, 127), ((9, 126), 0, 127), ((9, 127), 1, 43), ((9, 128), 0, 43),
   ((9, 129), 0, 13), ((9, 130), 0, 131), ((9, 131), 0, 11), ((9, 132), 0, 19), ((9, 133), 0, 67),
   ((9, 134), 1, 17), ((9, 135), 0, 17), ((9, 136), 0, 137), ((9, 137), 0, 23),
   ((9, 138), 0, 139), ((9, 139), 1, 47), ((9, 140), 0, 47), ((9, 141), 0, 71), ((9, 142), 0, 13),
   ((9, 143), 1, 29), ((9, 144), 0, 29), ((9, 145), 0, 73), ((9, 146), 1, 37), ((9, 147), 0, 37),
   ((9, 148), 0, 149), ((9, 149), 1, 151), ((9, 150), 0, 151), ((9, 151), 0, 19),
   ((9, 152), 0, 17), ((9, 153), 0, 11), ((9, 154), 0, 31), ((9, 155), 0, 13), ((9, 156), 0, 157),
   ((9, 157), 0, 79), ((9, 158), 0, 53), ((9, 159), 1, 23), ((9, 160), 0, 23), ((9, 161), 1, 163),
   ((9, 162), 0, 163), ((9, 163), 0, 41), ((9, 164), 0, 11), ((9, 165), 0, 83),
   ((9, 166), 0, 167), ((9, 167), 1, 13), ((9, 168), 0, 13), ((9, 169), 0, 17), ((9, 170), 0, 19),
   ((9, 171), 0, 43), ((9, 172), 0, 173), ((9, 173), 0, 29), ((9, 174), 1, 11), ((9, 175), 0, 11),
   ((9, 176), 0, 59), ((9, 177), 0, 89), ((9, 178), 0, 179), ((9, 179), 1, 181),
   ((9, 180), 0, 181), ((9, 181), 0, 13), ((9, 182), 0, 61), ((9, 183), 0, 23), ((9, 184), 0, 37),
   ((9, 185), 0, 31), ((9, 186), 0, 17), ((9, 187), 0, 47), ((9, 188), 1, 19), ((9, 189), 0, 19),
   ((9, 190), 0, 191), ((9, 191), 1, 193), ((9, 192), 0, 193), ((9, 193), 0, 97),
   ((9, 194), 0, 13), ((9, 195), 1, 197), ((9, 196), 0, 197), ((9, 197), 0, 11),
   ((9, 198), 0, 199), ((9, 199), 1, 67), ((10, 0), 0, 0), ((10, 1), 0, 0), ((10, 2), 0, 0),
   ((10, 3), 0, 0), ((10, 4), 0, 0), ((10, 5), 0, 0), ((10, 6), 0, 0), ((10, 7), 0, 0),
   ((10, 8), 0, 0), ((10, 9), 0, 0), ((10, 10), 0, 0), ((10, 11), 1, 13), ((10, 12), 0, 13),
   ((10, 13), 3, 17), ((10, 14), 2, 17), ((10, 15), 1, 17), ((10, 16), 0, 17), ((10, 17), 1, 19),
   ((10, 18), 0, 19), ((10, 19), 2, 11), ((10, 20), 1, 11), ((10, 21), 0, 11), ((10, 22), 0, 23),
   ((10, 23), 2, 13), ((10, 24), 1, 13), ((10, 25), 0, 13), ((10, 26), 2, 29), ((10, 27), 1, 29),
   ((10, 28), 0, 29), ((10, 29), 1, 31), ((10, 30), 0, 31), ((10, 31), 1, 11), ((10, 32), 0, 11),
   ((10, 33), 0, 17), ((10, 34), 2, 37), ((10, 35), 1, 37), ((10, 36), 0, 37), ((10, 37), 0, 19),
   ((10, 38), 0, 13), ((10, 39), 1, 41), ((10, 40), 0, 41), ((10, 41), 1, 43), ((10, 42), 0, 43),
   ((10, 43), 0, 11), ((10, 44), 1, 23), ((10, 45), 0, 23), ((10, 46), 0, 47), ((10, 47), 3, 17),
   ((10, 48), 2, 17), ((10, 49), 1, 17), ((10, 50), 0, 17), ((10, 51), 0, 13), ((10, 52), 0, 53),
   ((10, 53), 1, 11), ((10, 54), 0, 11), ((10, 55), 1, 19), ((10, 56), 0, 19), ((10, 57), 0, 29),
   ((10, 58), 0, 59), ((10, 59), 1, 61), ((10, 60), 0, 61), ((10, 61), 0, 31), ((10, 62), 2, 13),
   ((10, 63), 1, 13), ((10, 64), 0, 13), ((10, 65), 0, 11), ((10, 66), 0, 67), ((10, 67), 0, 17),
   ((10, 68), 0, 23), ((10, 69), 1, 71), ((10, 70), 0, 71), ((10, 71), 1, 73), ((10, 72), 0, 73),
   ((10, 73), 0, 37), ((10, 74), 1, 19), ((10, 75), 0, 19), ((10, 76), 0, 11), ((10, 77), 0, 13),
   ((10, 78), 0, 79), ((10, 79), 2, 41), ((10, 80), 1, 41), ((10, 81), 0, 41), ((10, 82), 0, 83),
   ((10, 83), 1, 17), ((10, 84), 0, 17), ((10, 85), 0, 43), ((10, 86), 0, 29), ((10, 87), 0, 11),
   ((10, 88), 0, 89), ((10, 89), 1, 13), ((10, 90), 0, 13), ((10, 91), 0, 23), ((10, 92), 0, 31),
   ((10, 93), 0, 47), ((10, 94), 0, 19), ((10, 95), 1, 97), ((10, 96), 0, 97), ((10, 97), 1, 11),
   ((10, 98), 0, 11), ((10, 99), 1, 101), ((10, 100), 0, 101), ((10, 101), 0, 17),
   ((10, 102), 0, 103), ((10, 103), 0, 13), ((10, 104), 1, 53), ((10, 105), 0, 53),
   ((10, 106), 0, 107), ((10, 107), 1, 109), ((10, 108), 0, 109), ((10, 109), 0, 11),
   ((10, 110), 0, 37), ((10, 111), 1, 113), ((10, 112), 0, 113), ((10, 113), 0, 19),
   ((10, 114), 0, 23), ((10, 115), 0, 29), ((10, 116), 0, 13), ((10, 117), 0, 59),
   ((10, 118), 0, 17), ((10, 119), 1, 11), ((10, 120), 0, 11), ((10, 121), 0, 61),
   ((10, 122), 0, 41), ((10, 123), 0, 31), ((10, 124), 2, 127), ((10, 125), 1, 127),
   ((10, 126), 0, 127), ((10, 127), 1, 43), ((10, 128), 0, 43), ((10, 129), 0, 13),
   ((10, 130), 0, 131), ((10, 131), 0, 11), ((10, 132), 0, 19), ((10, 133), 0, 67),
   ((10, 134), 1, 17), ((10, 135), 0, 17), ((10, 136), 0, 137), ((10, 137), 0, 23),
   ((10, 138), 0, 139), ((10, 139), 1, 47), ((10, 140), 0, 47), ((10, 141), 0, 71),
   ((10, 142), 0, 13), ((10, 143), 1, 29), ((10, 144), 0, 29), ((10, 145), 0, 73),
   ((10, 146), 1, 37), ((10, 147), 0, 37), ((10, 148), 0, 149), ((10, 149), 1, 151),
   ((10, 150), 0, 151), ((10, 151), 0, 19), ((10, 152), 0, 17), ((10, 153), 0, 11),
   ((10, 154), 0, 31), ((10, 155), 0, 13), ((10, 156), 0, 157), ((10, 157), 0, 79),
   ((10, 158), 0, 53), ((10, 159), 1, 23), ((10, 160), 0, 23), ((10, 161), 1, 163),
   ((10, 162), 0, 163), ((10, 163), 0, 41), ((10, 164), 0, 11), ((10, 165), 0, 83),
   ((10, 166), 0, 167), ((10, 167), 1, 13), ((10, 168), 0, 13), ((10, 169), 0, 17),
   ((10, 170), 0, 19), ((10, 171), 0, 43), ((10, 172), 0, 173), ((10, 173), 0, 29),
   ((10, 174), 1, 11), ((10, 175), 0, 11), ((10, 176), 0, 59), ((10, 177), 0, 89),
   ((10, 178), 0, 179), ((10, 179), 1, 181), ((10, 180), 0, 181), ((10, 181), 0, 13),
   ((10, 182), 0, 61), ((10, 183), 0, 23), ((10, 184), 0, 37), ((10, 185), 0, 31),
   ((10, 186), 0, 17), ((10, 187), 0, 47), ((10, 188), 1, 19), ((10, 189), 0, 19),
   ((10, 190), 0, 191), ((10, 191), 1, 193), ((10, 192), 0, 193), ((10, 193), 0, 97),
   ((10, 194), 0, 13), ((10, 195), 1, 197), ((10, 196), 0, 197), ((10, 197), 0, 11),
   ((10, 198), 0, 199), ((10, 199), 1, 67), ((11, 0), 0, 0), ((11, 1), 0, 0), ((11, 2), 0, 0),
   ((11, 3), 0, 0), ((11, 4), 0, 0), ((11, 5), 0, 0), ((11, 6), 0, 0), ((11, 7), 0, 0),
   ((11, 8), 0, 0), ((11, 9), 0, 0), ((11, 10), 0, 0), ((11, 11), 0, 0), ((11, 12), 0, 13),
   ((11, 13), 3, 17), ((11, 14), 2, 17), ((11, 15), 1, 17), ((11, 16), 0, 17), ((11, 17), 1, 19),
   ((11, 18), 0, 19), ((11, 19), 3, 23), ((11, 20), 2, 23), ((11, 21), 1, 23), ((11, 22), 0, 23),
   ((11, 23), 2, 13), ((11, 24), 1, 13), ((11, 25), 0, 13), ((11, 26), 2, 29), ((11, 27), 1, 29),
   ((11, 28), 0, 29), ((11, 29), 1, 31), ((11, 30), 0, 31), ((11, 31), 2, 17), ((11, 32), 1, 17),
   ((11, 33), 0, 17), ((11, 34), 2, 37), ((11, 35), 1, 37), ((11, 36), 0, 37), ((11, 37), 0, 19),
   ((11, 38), 0, 13), ((11, 39), 1, 41), ((11, 40), 0, 41), ((11, 41), 1, 43), ((11, 42), 0, 43),
   ((11, 43), 2, 23), ((11, 44), 1, 23), ((11, 45), 0, 23), ((11, 46), 0, 47), ((11, 47), 3, 17),
   ((11, 48), 2, 17), ((11, 49), 1, 17), ((11, 50), 0, 17), ((11, 51), 0, 13), ((11, 52), 0, 53),
   ((11, 53), 3, 19), ((11, 54), 2, 19), ((11, 55), 1, 19), ((11, 56), 0, 19), ((11, 57), 0, 29),
   ((11, 58), 0, 59), ((11, 59), 1, 61), ((11, 60), 0, 61), ((11, 61), 0, 31), ((11, 62), 2, 13),
   ((11, 63), 1, 13), ((11, 64), 0, 13), ((11, 65), 1, 67), ((11, 66), 0, 67), ((11, 67), 0, 17),
   ((11, 68), 0, 23), ((11, 69), 1, 71), ((11, 70), 0, 71), ((11, 71), 1, 73), ((11, 72), 0, 73),
   ((11, 73), 0, 37), ((11, 74), 1, 19), ((11, 75), 0, 19), ((11, 76), 1, 13), ((11, 77), 0, 13),
   ((11, 78), 0, 79), ((11, 79), 2, 41), ((11, 80), 1, 41), ((11, 81), 0, 41), ((11, 82), 0, 83),
   ((11, 83), 1, 17), ((11, 84), 0, 17), ((11, 85), 0, 43), ((11, 86), 0, 29), ((11, 87), 1, 89),
   ((11, 88), 0, 89), ((11, 89), 1, 13), ((11, 90), 0, 13), ((11, 91), 0, 23), ((11, 92), 0, 31),
   ((11, 93), 0, 47), ((11, 94), 0, 19), ((11, 95), 1, 97), ((11, 96), 0, 97), ((11, 97), 3, 101),
   ((11, 98), 2, 101), ((11, 99), 1, 101), ((11, 100), 0, 101), ((11, 101), 0, 17),
   ((11, 102), 0, 103), ((11, 103), 0, 13), ((11, 104), 1, 53), ((11, 105), 0, 53),
   ((11, 106), 0, 107), ((11, 107), 1, 109), ((11, 108), 0, 109), ((11, 109), 1, 37),
   ((11, 110), 0, 37), ((11, 111), 1, 113), ((11, 112), 0, 113), ((11, 113), 0, 19),
   ((11, 114), 0, 23), ((11, 115), 0, 29), ((11, 116), 0, 13), ((11, 117), 0, 59),
   ((11, 118), 0, 17), ((11, 119), 2, 61), ((11, 120), 1, 61), ((11, 121), 0, 61),
   ((11, 122), 0, 41), ((11, 123), 0, 31), ((11, 124), 2, 127), ((11, 125), 1, 127),
   ((11, 126), 0, 127), ((11, 127), 1, 43), ((11, 128), 0, 43), ((11, 129), 0, 13),
   ((11, 130), 0, 131), ((11, 131), 1, 19), ((11, 132), 0, 19), ((11, 133), 0, 67),
   ((11, 134), 1, 17), ((11, 135), 0, 17), ((11, 136), 0, 137), ((11, 137), 0, 23),
   ((11, 138), 0, 139), ((11, 139), 1, 47), ((11, 140), 0, 47), ((11, 141), 0, 71),
   ((11, 142), 0, 13), ((11, 143), 1, 29), ((11, 144), 0, 29), ((11, 145), 0, 73),
   ((11, 146), 1, 37), ((11, 147), 0, 37), ((11, 148), 0, 149), ((11, 149), 1, 151),
   ((11, 150), 0, 151), ((11, 151), 0, 19), ((11, 152), 0, 17), ((11, 153), 1, 31),
   ((11, 154), 0, 31), ((11, 155), 0, 13), ((11, 156), 0, 157), ((11, 157), 0, 79),
   ((11, 158), 0, 53), ((11, 159), 1, 23), ((11, 160), 0, 23), ((11, 161), 1, 163),
   ((11, 162), 0, 163), ((11, 163), 0, 41), ((11, 164), 1, 83), ((11, 165), 0, 83),
   ((11, 166), 0, 167), ((11, 167), 1, 13), ((11, 168), 0, 13), ((11, 169), 0, 17),
   ((11, 170), 0, 19), ((11, 171), 0, 43), ((11, 172), 0, 173), ((11, 173), 0, 29),
   ((11, 174), 2, 59), ((11, 175), 1, 59), ((11, 176), 0, 59), ((11, 177), 0, 89),
   ((11, 178), 0, 179), ((11, 179), 1, 181), ((11, 180), 0, 181), ((11, 181), 0, 13),
   ((11, 182), 0, 61), ((11, 183), 0, 23), ((11, 184), 0, 37), ((11, 185), 0, 31),
   ((11, 186), 0, 17), ((11, 187), 0, 47), ((11, 188), 1, 19), ((11, 189), 0, 19),
   ((11, 190), 0, 191), ((11, 191), 1, 193), ((11, 192), 0, 193), ((11, 193), 0, 97),
   ((11, 194), 0, 13), ((11, 195), 1, 197), ((11, 196), 0, 197), ((11, 197), 1, 199),
   ((11, 198), 0, 199), ((11, 199), 1, 67), ((12, 0), 0, 0), ((12, 1), 0, 0), ((12, 2), 0, 0),
   ((12, 3), 0, 0), ((12, 4), 0, 0), ((12, 5), 0, 0), ((12, 6), 0, 0), ((12, 7), 0, 0),
   ((12, 8), 0, 0), ((12, 9), 0, 0), ((12, 10), 0, 0), ((12, 11), 0, 0), ((12, 12), 0, 0),
   ((12, 13), 3, 17), ((12, 14), 2, 17), ((12, 15), 1, 17), ((12, 16), 0, 17), ((12, 17), 1, 19),
   ((12, 18), 0, 19), ((12, 19), 3, 23), ((12, 20), 2, 23), ((12, 21), 1, 23), ((12, 22), 0, 23),
   ((12, 23), 2, 13), ((12, 24), 1, 13), ((12, 25), 0, 13), ((12, 26), 2, 29), ((12, 27), 1, 29),
   ((12, 28), 0, 29), ((12, 29), 1, 31), ((12, 30), 0, 31), ((12, 31), 2, 17), ((12, 32), 1, 17),
   ((12, 33), 0, 17), ((12, 34), 2, 37), ((12, 35), 1, 37), ((12, 36), 0, 37), ((12, 37), 0, 19),
   ((12, 38), 0, 13), ((12, 39), 1, 41), ((12, 40), 0, 41), ((12, 41), 1, 43), ((12, 42), 0, 43),
   ((12, 43), 2, 23), ((12, 44), 1, 23), ((12, 45), 0, 23), ((12, 46), 0, 47), ((12, 47), 3, 17),
   ((12, 48), 2, 17), ((12, 49), 1, 17), ((12, 50), 0, 17), ((12, 51), 0, 13), ((12, 52), 0, 53),
   ((12, 53), 3, 19), ((12, 54), 2, 19), ((12, 55), 1, 19), ((12, 56), 0, 19), ((12, 57), 0, 29),
   ((12, 58), 0, 59), ((12, 59), 1, 61), ((12, 60), 0, 61), ((12, 61), 0, 31), ((12, 62), 2, 13),
   ((12, 63), 1, 13), ((12, 64), 0, 13), ((12, 65), 1, 67), ((12, 66), 0, 67), ((12, 67), 0, 17),
   ((12, 68), 0, 23), ((12, 69), 1, 71), ((12, 70), 0, 71), ((12, 71), 1, 73), ((12, 72), 0, 73),
   ((12, 73), 0, 37), ((12, 74), 1, 19), ((12, 75), 0, 19), ((12, 76), 1, 13), ((12, 77), 0, 13),
   ((12, 78), 0, 79), ((12, 79), 2, 41), ((12, 80), 1, 41), ((12, 81), 0, 41), ((12, 82), 0, 83),
   ((12, 83), 1, 17), ((12, 84), 0, 17), ((12, 85), 0, 43), ((12, 86), 0, 29), ((12, 87), 1, 89),
   ((12, 88), 0, 89), ((12, 89), 1, 13), ((12, 90), 0, 13), ((12, 91), 0, 23), ((12, 92), 0, 31),
   ((12, 93), 0, 47), ((12, 94), 0, 19), ((12, 95), 1, 97), ((12, 96), 0, 97), ((12, 97), 3, 101),
   ((12, 98), 2, 101), ((12, 99), 1, 101), ((12, 100), 0, 101), ((12, 101), 0, 17),
   ((12, 102), 0, 103), ((12, 103), 0, 13), ((12, 104), 1, 53), ((12, 105), 0, 53),
   ((12, 106), 0, 107), ((12, 107), 1, 109), ((12, 108), 0, 109), ((12, 109), 1, 37),
   ((12, 110), 0, 37), ((12, 111), 1, 113), ((12, 112), 0, 113), ((12, 113), 0, 19),
   ((12, 114), 0, 23), ((12, 115), 0, 29), ((12, 116), 0, 13), ((12, 117), 0, 59),
   ((12, 118), 0, 17), ((12, 119), 2, 61), ((12, 120), 1, 61), ((12, 121), 0, 61),
   ((12, 122), 0, 41), ((12, 123), 0, 31), ((12, 124), 2, 127), ((12, 125), 1, 127),
   ((12, 126), 0, 127), ((12, 127), 1, 43), ((12, 128), 0, 43), ((12, 129), 0, 13),
   ((12, 130), 0, 131), ((12, 131), 1, 19), ((12, 132), 0, 19), ((12, 133), 0, 67),
   ((12, 134), 1, 17), ((12, 135), 0, 17), ((12, 136), 0, 137), ((12, 137), 0, 23),
   ((12, 138), 0, 139), ((12, 139), 1, 47), ((12, 140), 0, 47), ((12, 141), 0, 71),
   ((12, 142), 0, 13), ((12, 143), 1, 29), ((12, 144), 0, 29), ((12, 145), 0, 73),
   ((12, 146), 1, 37), ((12, 147), 0, 37), ((12, 148), 0, 149), ((12, 149), 1, 151),
   ((12, 150), 0, 151), ((12, 151), 0, 19), ((12, 152), 0, 17), ((12, 153), 1, 31),
   ((12, 154), 0, 31), ((12, 155), 0, 13), ((12, 156), 0, 157), ((12, 157), 0, 79),
   ((12, 158), 0, 53), ((12, 159), 1, 23), ((12, 160), 0, 23), ((12, 161), 1, 163),
   ((12, 162), 0, 163), ((12, 163), 0, 41), ((12, 164), 1, 83), ((12, 165), 0, 83),
   ((12, 166), 0, 167), ((12, 167), 1, 13), ((12, 168), 0, 13), ((12, 169), 0, 17),
   ((12, 170), 0, 19), ((12, 171), 0, 43), ((12, 172), 0, 173), ((12, 173), 0, 29),
   ((12, 174), 2, 59), ((12, 175), 1, 59), ((12, 176), 0, 59), ((12, 177), 0, 89),
   ((12, 178), 0, 179), ((12, 179), 1, 181), ((12, 180), 0, 181), ((12, 181), 0, 13),
   ((12, 182), 0, 61), ((12, 183), 0, 23), ((12, 184), 0, 37), ((12, 185), 0, 31),
   ((12, 186), 0, 17), ((12, 187), 0, 47), ((12, 188), 1, 19), ((12, 189), 0, 19),
   ((12, 190), 0, 191), ((12, 191), 1, 193), ((12, 192), 0, 193), ((12, 193), 0, 97),
   ((12, 194), 0, 13), ((12, 195), 1, 197), ((12, 196), 0, 197), ((12, 197), 1, 199),
   ((12, 198), 0, 199), ((12, 199), 1, 67), ((13, 0), 0, 0), ((13, 1), 0, 0), ((13, 2), 0, 0),
   ((13, 3), 0, 0), ((13, 4), 0, 0), ((13, 5), 0, 0), ((13, 6), 0, 0), ((13, 7), 0, 0),
   ((13, 8), 0, 0), ((13, 9), 0, 0), ((13, 10), 0, 0), ((13, 11), 0, 0), ((13, 12), 0, 0),
   ((13, 13), 0, 0), ((13, 14), 2, 17), ((13, 15), 1, 17), ((13, 16), 0, 17), ((13, 17), 1, 19),
   ((13, 18), 0, 19), ((13, 19), 3, 23), ((13, 20), 2, 23), ((13, 21), 1, 23), ((13, 22), 0, 23),
   ((13, 23), 5, 29), ((13, 24), 4, 29), ((13, 25), 3, 29), ((13, 26), 2, 29), ((13, 27), 1, 29),
   ((13, 28), 0, 29), ((13, 29), 1, 31), ((13, 30), 0, 31), ((13, 31), 2, 17), ((13, 32), 1, 17),
   ((13, 33), 0, 17), ((13, 34), 2, 37), ((13, 35), 1, 37), ((13, 36), 0, 37), ((13, 37), 0, 19),
   ((13, 38), 2, 41), ((13, 39), 1, 41), ((13, 40), 0, 41), ((13, 41), 1, 43), ((13, 42), 0, 43),
   ((13, 43), 2, 23), ((13, 44), 1, 23), ((13, 45), 0, 23), ((13, 46), 0, 47), ((13, 47), 3, 17),
   ((13, 48), 2, 17), ((13, 49), 1, 17), ((13, 50), 0, 17), ((13, 51), 1, 53), ((13, 52), 0, 53),
   ((13, 53), 3, 19), ((13, 54), 2, 19), ((13, 55), 1, 19), ((13, 56), 0, 19), ((13, 57), 0, 29),
   ((13, 58), 0, 59), ((13, 59), 1, 61), ((13, 60), 0, 61), ((13, 61), 0, 31), ((13, 62), 4, 67),
   ((13, 63), 3, 67), ((13, 64), 2, 67), ((13, 65), 1, 67), ((13, 66), 0, 67), ((13, 67), 0, 17),
   ((13, 68), 0, 23), ((13, 69), 1, 71), ((13, 70), 0, 71), ((13, 71), 1, 73), ((13, 72), 0, 73),
   ((13, 73), 0, 37), ((13, 74), 1, 19), ((13, 75), 0, 19), ((13, 76), 2, 79), ((13, 77), 1, 79),
   ((13, 78), 0, 79), ((13, 79), 2, 41), ((13, 80), 1, 41), ((13, 81), 0, 41), ((13, 82), 0, 83),
   ((13, 83), 1, 17), ((13, 84), 0, 17), ((13, 85), 0, 43), ((13, 86), 0, 29), ((13, 87), 1, 89),
   ((13, 88), 0, 89), ((13, 89), 2, 23), ((13, 90), 1, 23), ((13, 91), 0, 23), ((13, 92), 0, 31),
   ((13, 93), 0, 47), ((13, 94), 0, 19), ((13, 95), 1, 97), ((13, 96), 0, 97), ((13, 97), 3, 101),
   ((13, 98), 2, 101), ((13, 99), 1, 101), ((13, 100), 0, 101), ((13, 101), 0, 17),
   ((13, 102), 0, 103), ((13, 103), 2, 53), ((13, 104), 1, 53), ((13, 105), 0, 53),
   ((13, 106), 0, 107), ((13, 107), 1, 109), ((13, 108), 0, 109), ((13, 109), 1, 37),
   ((13, 110), 0, 37), ((13, 111), 1, 113), ((13, 112), 0, 113), ((13, 113), 0, 19),
   ((13, 114), 0, 23), ((13, 115), 0, 29), ((13, 116), 1, 59), ((13, 117), 0, 59),
   ((13, 118), 0, 17), ((13, 119), 2, 61), ((13, 120), 1, 61), ((13, 121), 0, 61),
   ((13, 122), 0, 41), ((13, 123), 0, 31), ((13, 124), 2, 127), ((13, 125), 1, 127),
   ((13, 126), 0, 127), ((13, 127), 1, 43), ((13, 128), 0, 43), ((13, 129), 1, 131),
   ((13, 130), 0, 131), ((13, 131), 1, 19), ((13, 132), 0, 19), ((13, 133), 0, 67),
   ((13, 134), 1, 17), ((13, 135), 0, 17), ((13, 136), 0, 137), ((13, 137), 0, 23),
   ((13, 138), 0, 139), ((13, 139), 1, 47), ((13, 140), 0, 47), ((13, 141), 0, 71),
   ((13, 142), 2, 29), ((13, 143), 1, 29), ((13, 144), 0, 29), ((13, 145), 0, 73),
   ((13, 146), 1, 37), ((13, 147), 0, 37), ((13, 148), 0, 149), ((13, 149), 1, 151),
   ((13, 150), 0, 151), ((13, 151), 0, 19), ((13, 152), 0, 17), ((13, 153), 1, 31),
   ((13, 154), 0, 31), ((13, 155), 1, 157), ((13, 156), 0, 157), ((13, 157), 0, 79),
   ((13, 158), 0, 53), ((13, 159), 1, 23), ((13, 160), 0, 23), ((13, 161), 1, 163),
   ((13, 162), 0, 163), ((13, 163), 0, 41), ((13, 164), 1, 83), ((13, 165), 0, 83),
   ((13, 166), 0, 167), ((13, 167), 2, 17), ((13, 168), 1, 17), ((13, 169), 0, 17),
   ((13, 170), 0, 19), ((13, 171), 0, 43), ((13, 172), 0, 173), ((13, 173), 0, 29),
   ((13, 174), 2, 59), ((13, 175), 1, 59), ((13, 176), 0, 59), ((13, 177), 0, 89),
   ((13, 178), 0, 179), ((13, 179), 1, 181), ((13, 180), 0, 181), ((13, 181), 1, 61),
   ((13, 182), 0, 61), ((13, 183), 0, 23), ((13, 184), 0, 37), ((13, 185), 0, 31),
   ((13, 186), 0, 17), ((13, 187), 0, 47), ((13, 188), 1, 19), ((13, 189), 0, 19),
   ((13, 190), 0, 191), ((13, 191), 1, 193), ((13, 192), 0, 193), ((13, 193), 0, 97),
   ((13, 194), 2, 197), ((13, 195), 1, 197), ((13, 196), 0, 197), ((13, 197), 1, 199),
   ((13, 198), 0, 199), ((13, 199), 1, 67), ((14, 0), 0, 0), ((14, 1), 0, 0), ((14, 2), 0, 0),
   ((14, 3), 0, 0), ((14, 4), 0, 0), ((14, 5), 0, 0), ((14, 6), 0, 0), ((14, 7), 0, 0),
   ((14, 8), 0, 0), ((14, 9), 0, 0), ((14, 10), 0, 0), ((14, 11), 0, 0), ((14, 12), 0, 0),
   ((14, 13), 0, 0), ((14, 14), 0, 0), ((14, 15), 1, 17), ((14, 16), 0, 17), ((14, 17), 1, 19),
   ((14, 18), 0, 19), ((14, 19), 3, 23), ((14, 20), 2, 23), ((14, 21), 1, 23), ((14, 22), 0, 23),
   ((14, 23), 5, 29), ((14, 24), 4, 29), ((14, 25), 3, 29), ((14, 26), 2, 29), ((14, 27), 1, 29),
   ((14, 28), 0, 29), ((14, 29), 1, 31), ((14, 30), 0, 31), ((14, 31), 2, 17), ((14, 32), 1, 17),
   ((14, 33), 0, 17), ((14, 34), 2, 37), ((14, 35), 1, 37), ((14, 36), 0, 37), ((14, 37), 0, 19),
   ((14, 38), 2, 41), ((14, 39), 1, 41), ((14, 40), 0, 41), ((14, 41), 1, 43), ((14, 42), 0, 43),
   ((14, 43), 2, 23), ((14, 44), 1, 23), ((14, 45), 0, 23), ((14, 46), 0, 47), ((14, 47), 3, 17),
   ((14, 48), 2, 17), ((14, 49), 1, 17), ((14, 50), 0, 17), ((14, 51), 1, 53), ((14, 52), 0, 53),
   ((14, 53), 3, 19), ((14, 54), 2, 19), ((14, 55), 1, 19), ((14, 56), 0, 19), ((14, 57), 0, 29),
   ((14, 58), 0, 59), ((14, 59), 1, 61), ((14, 60), 0, 61), ((14, 61), 0, 31), ((14, 62), 4, 67),
   ((14, 63), 3, 67), ((14, 64), 2, 67), ((14, 65), 1, 67), ((14, 66), 0, 67), ((14, 67), 0, 17),
   ((14, 68), 0, 23), ((14, 69), 1, 71), ((14, 70), 0, 71), ((14, 71), 1, 73), ((14, 72), 0, 73),
   ((14, 73), 0, 37), ((14, 74), 1, 19), ((14, 75), 0, 19), ((14, 76), 2, 79), ((14, 77), 1, 79),
   ((14, 78), 0, 79), ((14, 79), 2, 41), ((14, 80), 1, 41), ((14, 81), 0, 41), ((14, 82), 0, 83),
   ((14, 83), 1, 17), ((14, 84), 0, 17), ((14, 85), 0, 43), ((14, 86), 0, 29), ((14, 87), 1, 89),
   ((14, 88), 0, 89), ((14, 89), 2, 23), ((14, 90), 1, 23), ((14, 91), 0, 23), ((14, 92), 0, 31),
   ((14, 93), 0, 47), ((14, 94), 0, 19), ((14, 95), 1, 97), ((14, 96), 0, 97), ((14, 97), 3, 101),
   ((14, 98), 2, 101), ((14, 99), 1, 101), ((14, 100), 0, 101), ((14, 101), 0, 17),
   ((14, 102), 0, 103), ((14, 103), 2, 53), ((14, 104), 1, 53), ((14, 105), 0, 53),
   ((14, 106), 0, 107), ((14, 107), 1, 109), ((14, 108), 0, 109), ((14, 109), 1, 37),
   ((14, 110), 0, 37), ((14, 111), 1, 113), ((14, 112), 0, 113), ((14, 113), 0, 19),
   ((14, 114), 0, 23), ((14, 115), 0, 29), ((14, 116), 1, 59), ((14, 117), 0, 59),
   ((14, 118), 0, 17), ((14, 119), 2, 61), ((14, 120), 1, 61), ((14, 121), 0, 61),
   ((14, 122), 0, 41), ((14, 123), 0, 31), ((14, 124), 2, 127), ((14, 125), 1, 127),
   ((14, 126), 0, 127), ((14, 127), 1, 43), ((14, 128), 0, 43), ((14, 129), 1, 131),
   ((14, 130), 0, 131), ((14, 131), 1, 19), ((14, 132), 0, 19), ((14, 133), 0, 67),
   ((14, 134), 1, 17), ((14, 135), 0, 17), ((14, 136), 0, 137), ((14, 137), 0, 23),
   ((14, 138), 0, 139), ((14, 139), 1, 47), ((14, 140), 0, 47), ((14, 141), 0, 71),
   ((14, 142), 2, 29), ((14, 143), 1, 29), ((14, 144), 0, 29), ((14, 145), 0, 73),
   ((14, 146), 1, 37), ((14, 147), 0, 37), ((14, 148), 0, 149), ((14, 149), 1, 151),
   ((14, 150), 0, 151), ((14, 151), 0, 19), ((14, 152), 0, 17), ((14, 153), 1, 31),
   ((14, 154), 0, 31), ((14, 155), 1, 157), ((14, 156), 0, 157), ((14, 157), 0, 79),
   ((14, 158), 0, 53), ((14, 159), 1, 23), ((14, 160), 0, 23), ((14, 161), 1, 163),
   ((14, 162), 0, 163), ((14, 163), 0, 41), ((14, 164), 1, 83), ((14, 165), 0, 83),
   ((14, 166), 0, 167), ((14, 167), 2, 17), ((14, 168), 1, 17), ((14, 169), 0, 17),
   ((14, 170), 0, 19), ((14, 171), 0, 43), ((14, 172), 0, 173), ((14, 173), 0, 29),
   ((14, 174), 2, 59), ((14, 175), 1, 59), ((14, 176), 0, 59), ((14, 177), 0, 89),
   ((14, 178), 0, 179), ((14, 179), 1, 181), ((14, 180), 0, 181), ((14, 181), 1, 61),
   ((14, 182), 0, 61), ((14, 183), 0, 23), ((14, 184), 0, 37), ((14, 185), 0, 31),
   ((14, 186), 0, 17), ((14, 187), 0, 47), ((14, 188), 1, 19), ((14, 189), 0, 19),
   ((14, 190), 0, 191), ((14, 191), 1, 193), ((14, 192), 0, 193), ((14, 193), 0, 97),
   ((14, 194), 2, 197), ((14, 195), 1, 197), ((14, 196), 0, 197), ((14, 197), 1, 199),
   ((14, 198), 0, 199), ((14, 199), 1, 67), ((15, 0), 0, 0), ((15, 1), 0, 0), ((15, 2), 0, 0),
   ((15, 3), 0, 0), ((15, 4), 0, 0), ((15, 5), 0, 0), ((15, 6), 0, 0), ((15, 7), 0, 0),
   ((15, 8), 0, 0), ((15, 9), 0, 0), ((15, 10), 0, 0), ((15, 11), 0, 0), ((15, 12), 0, 0),
   ((15, 13), 0, 0), ((15, 14), 0, 0), ((15, 15), 0, 0), ((15, 16), 0, 17), ((15, 17), 1, 19),
   ((15, 18), 0, 19), ((15, 19), 3, 23), ((15, 20), 2, 23), ((15, 21), 1, 23), ((15, 22), 0, 23),
   ((15, 23), 5, 29), ((15, 24), 4, 29), ((15, 25), 3, 29), ((15, 26), 2, 29), ((15, 27), 1, 29),
   ((15, 28), 0, 29), ((15, 29), 1, 31), ((15, 30), 0, 31), ((15, 31), 2, 17), ((15, 32), 1, 17),
   ((15, 33), 0, 17), ((15, 34), 2, 37), ((15, 35), 1, 37), ((15, 36), 0, 37), ((15, 37), 0, 19),
   ((15, 38), 2, 41), ((15, 39), 1, 41), ((15, 40), 0, 41), ((15, 41), 1, 43), ((15, 42), 0, 43),
   ((15, 43), 2, 23), ((15, 44), 1, 23), ((15, 45), 0, 23), ((15, 46), 0, 47), ((15, 47), 3, 17),
   ((15, 48), 2, 17), ((15, 49), 1, 17), ((15, 50), 0, 17), ((15, 51), 1, 53), ((15, 52), 0, 53),
   ((15, 53), 3, 19), ((15, 54), 2, 19), ((15, 55), 1, 19), ((15, 56), 0, 19), ((15, 57), 0, 29),
   ((15, 58), 0, 59), ((15, 59), 1, 61), ((15, 60), 0, 61), ((15, 61), 0, 31), ((15, 62), 4, 67),
   ((15, 63), 3, 67), ((15, 64), 2, 67), ((15, 65), 1, 67), ((15, 66), 0, 67), ((15, 67), 0, 17),
   ((15, 68), 0, 23), ((15, 69), 1, 71), ((15, 70), 0, 71), ((15, 71), 1, 73), ((15, 72), 0, 73),
   ((15, 73), 0, 37), ((15, 74), 1, 19), ((15, 75), 0, 19), ((15, 76), 2, 79), ((15, 77), 1, 79),
   ((15, 78), 0, 79), ((15, 79), 2, 41), ((15, 80), 1, 41), ((15, 81), 0, 41), ((15, 82), 0, 83),
   ((15, 83), 1, 17), ((15, 84), 0, 17), ((15, 85), 0, 43), ((15, 86), 0, 29), ((15, 87), 1, 89),
   ((15, 88), 0, 89), ((15, 89), 2, 23), ((15, 90), 1, 23), ((15, 91), 0, 23), ((15, 92), 0, 31),
   ((15, 93), 0, 47), ((15, 94), 0, 19), ((15, 95), 1, 97), ((15, 96), 0, 97), ((15, 97), 3, 101),
   ((15, 98), 2, 101), ((15, 99), 1, 101), ((15, 100), 0, 101), ((15, 101), 0, 17),
   ((15, 102), 0, 103), ((15, 103), 2, 53), ((15, 104), 1, 53), ((15, 105), 0, 53),
   ((15, 106), 0, 107), ((15, 107), 1, 109), ((15, 108), 0, 109), ((15, 109), 1, 37),
   ((15, 110), 0, 37), ((15, 111), 1, 113), ((15, 112), 0, 113), ((15, 113), 0, 19),
   ((15, 114), 0, 23), ((15, 115), 0, 29), ((15, 116), 1, 59), ((15, 117), 0, 59),
   ((15, 118), 0, 17), ((15, 119), 2, 61), ((15, 120), 1, 61), ((15, 121), 0, 61),
   ((15, 122), 0, 41), ((15, 123), 0, 31), ((15, 124), 2, 127), ((15, 125), 1, 127),
   ((15, 126), 0, 127), ((15, 127), 1, 43), ((15, 128), 0, 43), ((15, 129), 1, 131),
   ((15, 130), 0, 131), ((15, 131), 1, 19), ((15, 132), 0, 19), ((15, 133), 0, 67),
   ((15, 134), 1, 17), ((15, 135), 0, 17), ((15, 136), 0, 137), ((15, 137), 0, 23),
   ((15, 138), 0, 139), ((15, 139), 1, 47), ((15, 140), 0, 47), ((15, 141), 0, 71),
   ((15, 142), 2, 29), ((15, 143), 1, 29), ((15, 144), 0, 29), ((15, 145), 0, 73),
   ((15, 146), 1, 37), ((15, 147), 0, 37), ((15, 148), 0, 149), ((15, 149), 1, 151),
   ((15, 150), 0, 151), ((15, 151), 0, 19), ((15, 152), 0, 17), ((15, 153), 1, 31),
   ((15, 154), 0, 31), ((15, 155), 1, 157), ((15, 156), 0, 157), ((15, 157), 0, 79),
   ((15, 158), 0, 53), ((15, 159), 1, 23), ((15, 160), 0, 23), ((15, 161), 1, 163),
   ((15, 162), 0, 163), ((15, 163), 0, 41), ((15, 164), 1, 83), ((15, 165), 0, 83),
   ((15, 166), 0, 167), ((15, 167), 2, 17), ((15, 168), 1, 17), ((15, 169), 0, 17),
   ((15, 170), 0, 19), ((15, 171), 0, 43), ((15, 172), 0, 173), ((15, 173), 0, 29),
   ((15, 174), 2, 59), ((15, 175), 1, 59), ((15, 176), 0, 59), ((15, 177), 0, 89),
   ((15, 178), 0, 179), ((15, 179), 1, 181), ((15, 180), 0, 181), ((15, 181), 1, 61),
   ((15, 182), 0, 61), ((15, 183), 0, 23), ((15, 184), 0, 37), ((15, 185), 0, 31),
   ((15, 186), 0, 17), ((15, 187), 0, 47), ((15, 188), 1, 19), ((15, 189), 0, 19),
   ((15, 190), 0, 191), ((15, 191), 1, 193), ((15, 192), 0, 193), ((15, 193), 0, 97),
   ((15, 194), 2, 197), ((15, 195), 1, 197), ((15, 196), 0, 197), ((15, 197), 1, 199),
   ((15, 198), 0, 199), ((15, 199), 1, 67), ((16, 0), 0, 0), ((16, 1), 0, 0), ((16, 2), 0, 0),
   ((16, 3), 0, 0), ((16, 4), 0, 0), ((16, 5), 0, 0), ((16, 6), 0, 0), ((16, 7), 0, 0),
   ((16, 8), 0, 0), ((16, 9), 0, 0), ((16, 10), 0, 0), ((16, 11), 0, 0), ((16, 12), 0, 0),
   ((16, 13), 0, 0), ((16, 14), 0, 0), ((16, 15), 0, 0), ((16, 16), 0, 0), ((16, 17), 1, 19),
   ((16, 18), 0, 19), ((16, 19), 3, 23), ((16, 20), 2, 23), ((16, 21), 1, 23), ((16, 22), 0, 23),
   ((16, 23), 5, 29), ((16, 24), 4, 29), ((16, 25), 3, 29), ((16, 26), 2, 29), ((16, 27), 1, 29),
   ((16, 28), 0, 29), ((16, 29), 1, 31), ((16, 30), 0, 31), ((16, 31), 2, 17), ((16, 32), 1, 17),
   ((16, 33), 0, 17), ((16, 34), 2, 37), ((16, 35), 1, 37), ((16, 36), 0, 37), ((16, 37), 0, 19),
   ((16, 38), 2, 41), ((16, 39), 1, 41), ((16, 40), 0, 41), ((16, 41), 1, 43), ((16, 42), 0, 43),
   ((16, 43), 2, 23), ((16, 44), 1, 23), ((16, 45), 0, 23), ((16, 46), 0, 47), ((16, 47), 3, 17),
   ((16, 48), 2, 17), ((16, 49), 1, 17), ((16, 50), 0, 17), ((16, 51), 1, 53), ((16, 52), 0, 53),
   ((16, 53), 3, 19), ((16, 54), 2, 19), ((16, 55), 1, 19), ((16, 56), 0, 19), ((16, 57), 0, 29),
   ((16, 58), 0, 59), ((16, 59), 1, 61), ((16, 60), 0, 61), ((16, 61), 0, 31), ((16, 62), 4, 67),
   ((16, 63), 3, 67), ((16, 64), 2, 67), ((16, 65), 1, 67), ((16, 66), 0, 67), ((16, 67), 0, 17),
   ((16, 68), 0, 23), ((16, 69), 1, 71), ((16, 70), 0, 71), ((16, 71), 1, 73), ((16, 72), 0, 73),
   ((16, 73), 0, 37), ((16, 74), 1, 19), ((16, 75), 0, 19), ((16, 76), 2, 79), ((16, 77), 1, 79),
   ((16, 78), 0, 79), ((16, 79), 2, 41), ((16, 80), 1, 41), ((16, 81), 0, 41), ((16, 82), 0, 83),
   ((16, 83), 1, 17), ((16, 84), 0, 17), ((16, 85), 0, 43), ((16, 86), 0, 29), ((16, 87), 1, 89),
   ((16, 88), 0, 89), ((16, 89), 2, 23), ((16, 90), 1, 23), ((16, 91), 0, 23), ((16, 92), 0, 31),
   ((16, 93), 0, 47), ((16, 94), 0, 19), ((16, 95), 1, 97), ((16, 96), 0, 97), ((16, 97), 3, 101),
   ((16, 98), 2, 101), ((16, 99), 1, 101), ((16, 100), 0, 101), ((16, 101), 0, 17),
   ((16, 102), 0, 103), ((16, 103), 2, 53), ((16, 104), 1, 53), ((16, 105), 0, 53),
   ((16, 106), 0, 107), ((16, 107), 1, 109), ((16, 108), 0, 109), ((16, 109), 1, 37),
   ((16, 110), 0, 37), ((16, 111), 1, 113), ((16, 112), 0, 113), ((16, 113), 0, 19),
   ((16, 114), 0, 23), ((16, 115), 0, 29), ((16, 116), 1, 59), ((16, 117), 0, 59),
   ((16, 118), 0, 17), ((16, 119), 2, 61), ((16, 120), 1, 61), ((16, 121), 0, 61),
   ((16, 122), 0, 41), ((16, 123), 0, 31), ((16, 124), 2, 127), ((16, 125), 1, 127),
   ((16, 126), 0, 127), ((16, 127), 1, 43), ((16, 128), 0, 43), ((16, 129), 1, 131),
   ((16, 130), 0, 131), ((16, 131), 1, 19), ((16, 132), 0, 19), ((16, 133), 0, 67),
   ((16, 134), 1, 17), ((16, 135), 0, 17), ((16, 136), 0, 137), ((16, 137), 0, 23),
   ((16, 138), 0, 139), ((16, 139), 1, 47), ((16, 140), 0, 47), ((16, 141), 0, 71),
   ((16, 142), 2, 29), ((16, 143), 1, 29), ((16, 144), 0, 29), ((16, 145), 0, 73),
   ((16, 146), 1, 37), ((16, 147), 0, 37), ((16, 148), 0, 149), ((16, 149), 1, 151),
   ((16, 150), 0, 151), ((16, 151), 0, 19), ((16, 152), 0, 17), ((16, 153), 1, 31),
   ((16, 154), 0, 31), ((16, 155), 1, 157), ((16, 156), 0, 157), ((16, 157), 0, 79),
   ((16, 158), 0, 53), ((16, 159), 1, 23), ((16, 160), 0, 23), ((16, 161), 1, 163),
   ((16, 162), 0, 163), ((16, 163), 0, 41), ((16, 164), 1, 83), ((16, 165), 0, 83),
   ((16, 166), 0, 167), ((16, 167), 2, 17), ((16, 168), 1, 17), ((16, 169), 0, 17),
   ((16, 170), 0, 19), ((16, 171), 0, 43), ((16, 172), 0, 173), ((16, 173), 0, 29),
   ((16, 174), 2, 59), ((16, 175), 1, 59), ((16, 176), 0, 59), ((16, 177), 0, 89),
   ((16, 178), 0, 179), ((16, 179), 1, 181), ((16, 180), 0, 181), ((16, 181), 1, 61),
   ((16, 182), 0, 61), ((16, 183), 0, 23), ((16, 184), 0, 37), ((16, 185), 0, 31),
   ((16, 186), 0, 17), ((16, 187), 0, 47), ((16, 188), 1, 19), ((16, 189), 0, 19),
   ((16, 190), 0, 191), ((16, 191), 1, 193), ((16, 192), 0, 193), ((16, 193), 0, 97),
   ((16, 194), 2, 197), ((16, 195), 1, 197), ((16, 196), 0, 197), ((16, 197), 1, 199),
   ((16, 198), 0, 199), ((16, 199), 1, 67), ((17, 0), 0, 0), ((17, 1), 0, 0), ((17, 2), 0, 0),
   ((17, 3), 0, 0), ((17, 4), 0, 0), ((17, 5), 0, 0), ((17, 6), 0, 0), ((17, 7), 0, 0),
   ((17, 8), 0, 0), ((17, 9), 0, 0), ((17, 10), 0, 0), ((17, 11), 0, 0), ((17, 12), 0, 0),
   ((17, 13), 0, 0), ((17, 14), 0, 0), ((17, 15), 0, 0), ((17, 16), 0, 0), ((17, 17), 0, 0),
   ((17, 18), 0, 19), ((17, 19), 3, 23), ((17, 20), 2, 23), ((17, 21), 1, 23), ((17, 22), 0, 23),
   ((17, 23), 5, 29), ((17, 24), 4, 29), ((17, 25), 3, 29), ((17, 26), 2, 29), ((17, 27), 1, 29),
   ((17, 28), 0, 29), ((17, 29), 1, 31), ((17, 30), 0, 31), ((17, 31), 5, 37), ((17, 32), 4, 37),
   ((17, 33), 3, 37), ((17, 34), 2, 37), ((17, 35), 1, 37), ((17, 36), 0, 37), ((17, 37), 0, 19),
   ((17, 38), 2, 41), ((17, 39), 1, 41), ((17, 40), 0, 41), ((17, 41), 1, 43), ((17, 42), 0, 43),
   ((17, 43), 2, 23), ((17, 44), 1, 23), ((17, 45), 0, 23), ((17, 46), 0, 47), ((17, 47), 5, 53),
   ((17, 48), 4, 53), ((17, 49), 3, 53), ((17, 50), 2, 53), ((17, 51), 1, 53), ((17, 52), 0, 53),
   ((17, 53), 3, 19), ((17, 54), 2, 19), ((17, 55), 1, 19), ((17, 56), 0, 19), ((17, 57), 0, 29),
   ((17, 58), 0, 59), ((17, 59), 1, 61), ((17, 60), 0, 61), ((17, 61), 0, 31), ((17, 62), 4, 67),
   ((17, 63), 3, 67), ((17, 64), 2, 67), ((17, 65), 1, 67), ((17, 66), 0, 67), ((17, 67), 1, 23),
   ((17, 68), 0, 23), ((17, 69), 1, 71), ((17, 70), 0, 71), ((17, 71), 1, 73), ((17, 72), 0, 73),
   ((17, 73), 0, 37), ((17, 74), 1, 19), ((17, 75), 0, 19), ((17, 76), 2, 79), ((17, 77), 1, 79),
   ((17, 78), 0, 79), ((17, 79), 2, 41), ((17, 80), 1, 41), ((17, 81), 0, 41), ((17, 82), 0, 83),
   ((17, 83), 2, 43), ((17, 84), 1, 43), ((17, 85), 0, 43), ((17, 86), 0, 29), ((17, 87), 1, 89),
   ((17, 88), 0, 89), ((17, 89), 2, 23), ((17, 90), 1, 23), ((17, 91), 0, 23), ((17, 92), 0, 31),
   ((17, 93), 0, 47), ((17, 94), 0, 19), ((17, 95), 1, 97), ((17, 96), 0, 97), ((17, 97), 3, 101),
   ((17, 98), 2, 101), ((17, 99), 1, 101), ((17, 100), 0, 101), ((17, 101), 1, 103),
   ((17, 102), 0, 103), ((17, 103), 2, 53), ((17, 104), 1, 53), ((17, 105), 0, 53),
   ((17, 106), 0, 107), ((17, 107), 1, 109), ((17, 108), 0, 109), ((17, 109), 1, 37),
   ((17, 110), 0, 37), ((17, 111), 1, 113), ((17, 112), 0, 113), ((17, 113), 0, 19),
   ((17, 114), 0, 23), ((17, 115), 0, 29), ((17, 116), 1, 59), ((17, 117), 0, 59),
   ((17, 118), 3, 61), ((17, 119), 2, 61), ((17, 120), 1, 61), ((17, 121), 0, 61),
   ((17, 122), 0, 41), ((17, 123), 0, 31), ((17, 124), 2, 127), ((17, 125), 1, 127),
   ((17, 126), 0, 127), ((17, 127), 1, 43), ((17, 128), 0, 43), ((17, 129), 1, 131),
   ((17, 130), 0, 131), ((17, 131), 1, 19), ((17, 132), 0, 19), ((17, 133), 0, 67),
   ((17, 134), 2, 137), ((17, 135), 1, 137), ((17, 136), 0, 137), ((17, 137), 0, 23),
   ((17, 138), 0, 139), ((17, 139), 1, 47), ((17, 140), 0, 47), ((17, 141), 0, 71),
   ((17, 142), 2, 29), ((17, 143), 1, 29), ((17, 144), 0, 29), ((17, 145), 0, 73),
   ((17, 146), 1, 37), ((17, 147), 0, 37), ((17, 148), 0, 149), ((17, 149), 1, 151),
   ((17, 150), 0, 151), ((17, 151), 0, 19), ((17, 152), 2, 31), ((17, 153), 1, 31),
   ((17, 154), 0, 31), ((17, 155), 1, 157), ((17, 156), 0, 157), ((17, 157), 0, 79),
   ((17, 158), 0, 53), ((17, 159), 1, 23), ((17, 160), 0, 23), ((17, 161), 1, 163),
   ((17, 162), 0, 163), ((17, 163), 0, 41), ((17, 164), 1, 83), ((17, 165), 0, 83),
   ((17, 166), 0, 167), ((17, 167), 3, 19), ((17, 168), 2, 19), ((17, 169), 1, 19),
   ((17, 170), 0, 19), ((17, 171), 0, 43), ((17, 172), 0, 173), ((17, 173), 0, 29),
   ((17, 174), 2, 59), ((17, 175), 1, 59), ((17, 176), 0, 59), ((17, 177), 0, 89),
   ((17, 178), 0, 179), ((17, 179), 1, 181), ((17, 180), 0, 181), ((17, 181), 1, 61),
   ((17, 182), 0, 61), ((17, 183), 0, 23), ((17, 184), 0, 37), ((17, 185), 0, 31),
   ((17, 186), 1, 47), ((17, 187), 0, 47), ((17, 188), 1, 19), ((17, 189), 0, 19),
   ((17, 190), 0, 191), ((17, 191), 1, 193), ((17, 192), 0, 193), ((17, 193), 0, 97),
   ((17, 194), 2, 197), ((17, 195), 1, 197), ((17, 196), 0, 197), ((17, 197), 1, 199),
   ((17, 198), 0, 199), ((17, 199), 1, 67), ((18, 0), 0, 0), ((18, 1), 0, 0), ((18, 2), 0, 0),
   ((18, 3), 0, 0), ((18, 4), 0, 0), ((18, 5), 0, 0), ((18, 6), 0, 0), ((18, 7), 0, 0),
   ((18, 8), 0, 0), ((18, 9), 0, 0), ((18, 10), 0, 0), ((18, 11), 0, 0), ((18, 12), 0, 0),
   ((18, 13), 0, 0), ((18, 14), 0, 0), ((18, 15), 0, 0), ((18, 16), 0, 0), ((18, 17), 0, 0),
   ((18, 18), 0, 0), ((18, 19), 3, 23), ((18, 20), 2, 23), ((18, 21), 1, 23), ((18, 22), 0, 23),
   ((18, 23), 5, 29), ((18, 24), 4, 29), ((18, 25), 3, 29), ((18, 26), 2, 29), ((18, 27), 1, 29),
   ((18, 28), 0, 29), ((18, 29), 1, 31), ((18, 30), 0, 31), ((18, 31), 5, 37), ((18, 32), 4, 37),
   ((18, 33), 3, 37), ((18, 34), 2, 37), ((18, 35), 1, 37), ((18, 36), 0, 37), ((18, 37), 0, 19),
   ((18, 38), 2, 41), ((18, 39), 1, 41), ((18, 40), 0, 41), ((18, 41), 1, 43), ((18, 42), 0, 43),
   ((18, 43), 2, 23), ((18, 44), 1, 23), ((18, 45), 0, 23), ((18, 46), 0, 47), ((18, 47), 5, 53),
   ((18, 48), 4, 53), ((18, 49), 3, 53), ((18, 50), 2, 53), ((18, 51), 1, 53), ((18, 52), 0, 53),
   ((18, 53), 3, 19), ((18, 54), 2, 19), ((18, 55), 1, 19), ((18, 56), 0, 19), ((18, 57), 0, 29),
   ((18, 58), 0, 59), ((18, 59), 1, 61), ((18, 60), 0, 61), ((18, 61), 0, 31), ((18, 62), 4, 67),
   ((18, 63), 3, 67), ((18, 64), 2, 67), ((18, 65), 1, 67), ((18, 66), 0, 67), ((18, 67), 1, 23),
   ((18, 68), 0, 23), ((18, 69), 1, 71), ((18, 70), 0, 71), ((18, 71), 1, 73), ((18, 72), 0, 73),
   ((18, 73), 0, 37), ((18, 74), 1, 19), ((18, 75), 0, 19), ((18, 76), 2, 79), ((18, 77), 1, 79),
   ((18, 78), 0, 79), ((18, 79), 2, 41), ((18, 80), 1, 41), ((18, 81), 0, 41), ((18, 82), 0, 83),
   ((18, 83), 2, 43), ((18, 84), 1, 43), ((18, 85), 0, 43), ((18, 86), 0, 29), ((18, 87), 1, 89),
   ((18, 88), 0, 89), ((18, 89), 2, 23), ((18, 90), 1, 23), ((18, 91), 0, 23), ((18, 92), 0, 31),
   ((18, 93), 0, 47), ((18, 94), 0, 19), ((18, 95), 1, 97), ((18, 96), 0, 97), ((18, 97), 3, 101),
   ((18, 98), 2, 101), ((18, 99), 1, 101), ((18, 100), 0, 101), ((18, 101), 1, 103),
   ((18, 102), 0, 103), ((18, 103), 2, 53), ((18, 104), 1, 53), ((18, 105), 0, 53),
   ((18, 106), 0, 107), ((18, 107), 1, 109), ((18, 108), 0, 109), ((18, 109), 1, 37),
   ((18, 110), 0, 37), ((18, 111), 1, 113), ((18, 112), 0, 113), ((18, 113), 0, 19),
   ((18, 114), 0, 23), ((18, 115), 0, 29), ((18, 116), 1, 59), ((18, 117), 0, 59),
   ((18, 118), 3, 61), ((18, 119), 2, 61), ((18, 120), 1, 61), ((18, 121), 0, 61),
   ((18, 122), 0, 41), ((18, 123), 0, 31), ((18, 124), 2, 127), ((18, 125), 1, 127),
   ((18, 126), 0, 127), ((18, 127), 1, 43), ((18, 128), 0, 43), ((18, 129), 1, 131),
   ((18, 130), 0, 131), ((18, 131), 1, 19), ((18, 132), 0, 19), ((18, 133), 0, 67),
   ((18, 134), 2, 137), ((18, 135), 1, 137), ((18, 136), 0, 137), ((18, 137), 0, 23),
   ((18, 138), 0, 139), ((18, 139), 1, 47), ((18, 140), 0, 47), ((18, 141), 0, 71),
   ((18, 142), 2, 29), ((18, 143), 1, 29), ((18, 144), 0, 29), ((18, 145), 0, 73),
   ((18, 146), 1, 37), ((18, 147), 0, 37), ((18, 148), 0, 149), ((18, 149), 1, 151),
   ((18, 150), 0, 151), ((18, 151), 0, 19), ((18, 152), 2, 31), ((18, 153), 1, 31),
   ((18, 154), 0, 31), ((18, 155), 1, 157), ((18, 156), 0, 157), ((18, 157), 0, 79),
   ((18, 158), 0, 53), ((18, 159), 1, 23), ((18, 160), 0, 23), ((18, 161), 1, 163),
   ((18, 162), 0, 163), ((18, 163), 0, 41), ((18, 164), 1, 83), ((18, 165), 0, 83),
   ((18, 166), 0, 167), ((18, 167), 3, 19), ((18, 168), 2, 19), ((18, 169), 1, 19),
   ((18, 170), 0, 19), ((18, 171), 0, 43), ((18, 172), 0, 173), ((18, 173), 0, 29),
   ((18, 174), 2, 59), ((18, 175), 1, 59), ((18, 176), 0, 59), ((18, 177), 0, 89),
   ((18, 178), 0, 179), ((18, 179), 1, 181), ((18, 180), 0, 181), ((18, 181), 1, 61),
   ((18, 182), 0, 61), ((18, 183), 0, 23), ((18, 184), 0, 37), ((18, 185), 0, 31),
   ((18, 186), 1, 47), ((18, 187), 0, 47), ((18, 188), 1, 19), ((18, 189), 0, 19),
   ((18, 190), 0, 191), ((18, 191), 1, 193), ((18, 192), 0, 193), ((18, 193), 0, 97),
   ((18, 194), 2, 197), ((18, 195), 1, 197), ((18, 196), 0, 197), ((18, 197), 1, 199),
   ((18, 198), 0, 199), ((18, 199), 1, 67), ((19, 0), 0, 0), ((19, 1), 0, 0), ((19, 2), 0, 0),
   ((19, 3), 0, 0), ((19, 4), 0, 0), ((19, 5), 0, 0), ((19, 6), 0, 0), ((19, 7), 0, 0),
   ((19, 8), 0, 0), ((19, 9), 0, 0), ((19, 10), 0, 0), ((19, 11), 0, 0), ((19, 12), 0, 0),
   ((19, 13), 0, 0), ((19, 14), 0, 0), ((19, 15), 0, 0), ((19, 16), 0, 0), ((19, 17), 0, 0),
   ((19, 18), 0, 0), ((19, 19), 0, 0), ((19, 20), 2, 23), ((19, 21), 1, 23), ((19, 22), 0, 23),
   ((19, 23), 5, 29), ((19, 24), 4, 29), ((19, 25), 3, 29), ((19, 26), 2, 29), ((19, 27), 1, 29),
   ((19, 28), 0, 29), ((19, 29), 1, 31), ((19, 30), 0, 31), ((19, 31), 5, 37), ((19, 32), 4, 37),
   ((19, 33), 3, 37), ((19, 34), 2, 37), ((19, 35), 1, 37), ((19, 36), 0, 37), ((19, 37), 3, 41),
   ((19, 38), 2, 41), ((19, 39), 1, 41), ((19, 40), 0, 41), ((19, 41), 1, 43), ((19, 42), 0, 43),
   ((19, 43), 2, 23), ((19, 44), 1, 23), ((19, 45), 0, 23), ((19, 46), 0, 47), ((19, 47), 5, 53),
   ((19, 48), 4, 53), ((19, 49), 3, 53), ((19, 50), 2, 53), ((19, 51), 1, 53), ((19, 52), 0, 53),
   ((19, 53), 4, 29), ((19, 54), 3, 29), ((19, 55), 2, 29), ((19, 56), 1, 29), ((19, 57), 0, 29),
   ((19, 58), 0, 59), ((19, 59), 1, 61), ((19, 60), 0, 61), ((19, 61), 0, 31), ((19, 62), 4, 67),
   ((19, 63), 3, 67), ((19, 64), 2, 67), ((19, 65), 1, 67), ((19, 66), 0, 67), ((19, 67), 1, 23),
   ((19, 68), 0, 23), ((19, 69), 1, 71), ((19, 70), 0, 71), ((19, 71), 1, 73), ((19, 72), 0, 73),
   ((19, 73), 0, 37), ((19, 74), 4, 79), ((19, 75), 3, 79), ((19, 76), 2, 79), ((19, 77), 1, 79),
   ((19, 78), 0, 79), ((19, 79), 2, 41), ((19, 80), 1, 41), ((19, 81), 0, 41), ((19, 82), 0, 83),
   ((19, 83), 2, 43), ((19, 84), 1, 43), ((19, 85), 0, 43), ((19, 86), 0, 29), ((19, 87), 1, 89),
   ((19, 88), 0, 89), ((19, 89), 2, 23), ((19, 90), 1, 23), ((19, 91), 0, 23), ((19, 92), 0, 31),
   ((19, 93), 0, 47), ((19, 94), 2, 97), ((19, 95), 1, 97), ((19, 96), 0, 97), ((19, 97), 3, 101),
   ((19, 98), 2, 101), ((19, 99), 1, 101), ((19, 100), 0, 101), ((19, 101), 1, 103),
   ((19, 102), 0, 103), ((19, 103), 2, 53), ((19, 104), 1, 53), ((19, 105), 0, 53),
   ((19, 106), 0, 107), ((19, 107), 1, 109), ((19, 108), 0, 109), ((19, 109), 1, 37),
   ((19, 110), 0, 37), ((19, 111), 1, 113), ((19, 112), 0, 113), ((19, 113), 1, 23),
   ((19, 114), 0, 23), ((19, 115), 0, 29), ((19, 116), 1, 59), ((19, 117), 0, 59),
   ((19, 118), 3, 61), ((19, 119), 2, 61), ((19, 120), 1, 61), ((19, 121), 0, 61),
   ((19, 122), 0, 41), ((19, 123), 0, 31), ((19, 124), 2, 127), ((19, 125), 1, 127),
   ((19, 126), 0, 127), ((19, 127), 1, 43), ((19, 128), 0, 43), ((19, 129), 1, 131),
   ((19, 130), 0, 131), ((19, 131), 2, 67), ((19, 132), 1, 67), ((19, 133), 0, 67),
   ((19, 134), 2, 137), ((19, 135), 1, 137), ((19, 136), 0, 137), ((19, 137), 0, 23),
   ((19, 138), 0, 139), ((19, 139), 1, 47), ((19, 140), 0, 47), ((19, 141), 0, 71),
   ((19, 142), 2, 29), ((19, 143), 1, 29), ((19, 144), 0, 29), ((19, 145), 0, 73),
   ((19, 146), 1, 37), ((19, 147), 0, 37), ((19, 148), 0, 149), ((19, 149), 1, 151),
   ((19, 150), 0, 151), ((19, 151), 3, 31), ((19, 152), 2, 31), ((19, 153), 1, 31),
   ((19, 154), 0, 31), ((19, 155), 1, 157), ((19, 156), 0, 157), ((19, 157), 0, 79),
   ((19, 158), 0, 53), ((19, 159), 1, 23), ((19, 160), 0, 23), ((19, 161), 1, 163),
   ((19, 162), 0, 163), ((19, 163), 0, 41), ((19, 164), 1, 83), ((19, 165), 0, 83),
   ((19, 166), 0, 167), ((19, 167), 4, 43), ((19, 168), 3, 43), ((19, 169), 2, 43),
   ((19, 170), 1, 43), ((19, 171), 0, 43), ((19, 172), 0, 173), ((19, 173), 0, 29),
   ((19, 174), 2, 59), ((19, 175), 1, 59), ((19, 176), 0, 59), ((19, 177), 0, 89),
   ((19, 178), 0, 179), ((19, 179), 1, 181), ((19, 180), 0, 181), ((19, 181), 1, 61),
   ((19, 182), 0, 61), ((19, 183), 0, 23), ((19, 184), 0, 37), ((19, 185), 0, 31),
   ((19, 186), 1, 47), ((19, 187), 0, 47), ((19, 188), 2, 191), ((19, 189), 1, 191),
   ((19, 190), 0, 191), ((19, 191), 1, 193), ((19, 192), 0, 193), ((19, 193), 0, 97),
   ((19, 194), 2, 197), ((19, 195), 1, 197), ((19, 196), 0, 197), ((19, 197), 1, 199),
   ((19, 198), 0, 199), ((19, 199), 1, 67), ((20, 0), 0, 0), ((20, 1), 0, 0), ((20, 2), 0, 0),
   ((20, 3), 0, 0), ((20, 4), 0, 0), ((20, 5), 0, 0), ((20, 6), 0, 0), ((20, 7), 0, 0),
   ((20, 8), 0, 0), ((20, 9), 0, 0), ((20, 10), 0, 0), ((20, 11), 0, 0), ((20, 12), 0, 0),
   ((20, 13), 0, 0), ((20, 14), 0, 0), ((20, 15), 0, 0), ((20, 16), 0, 0), ((20, 17), 0, 0),
   ((20, 18), 0, 0), ((20, 19), 0, 0), ((20, 20), 0, 0), ((20, 21), 1, 23), ((20, 22), 0, 23),
   ((20, 23), 5, 29), ((20, 24), 4, 29), ((20, 25), 3, 29), ((20, 26), 2, 29), ((20, 27), 1, 29),
   ((20, 28), 0, 29), ((20, 29), 1, 31), ((20, 30), 0, 31), ((20, 31), 5, 37), ((20, 32), 4, 37),
   ((20, 33), 3, 37), ((20, 34), 2, 37), ((20, 35), 1, 37), ((20, 36), 0, 37), ((20, 37), 3, 41),
   ((20, 38), 2, 41), ((20, 39), 1, 41), ((20, 40), 0, 41), ((20, 41), 1, 43), ((20, 42), 0, 43),
   ((20, 43), 2, 23), ((20, 44), 1, 23), ((20, 45), 0, 23), ((20, 46), 0, 47), ((20, 47), 5, 53),
   ((20, 48), 4, 53), ((20, 49), 3, 53), ((20, 50), 2, 53), ((20, 51), 1, 53), ((20, 52), 0, 53),
   ((20, 53), 4, 29), ((20, 54), 3, 29), ((20, 55), 2, 29), ((20, 56), 1, 29), ((20, 57), 0, 29),
   ((20, 58), 0, 59), ((20, 59), 1, 61), ((20, 60), 0, 61), ((20, 61), 0, 31), ((20, 62), 4, 67),
   ((20, 63), 3, 67), ((20, 64), 2, 67), ((20, 65), 1, 67), ((20, 66), 0, 67), ((20, 67), 1, 23),
   ((20, 68), 0, 23), ((20, 69), 1, 71), ((20, 70), 0, 71), ((20, 71), 1, 73), ((20, 72), 0, 73),
   ((20, 73), 0, 37), ((20, 74), 4, 79), ((20, 75), 3, 79), ((20, 76), 2, 79), ((20, 77), 1, 79),
   ((20, 78), 0, 79), ((20, 79), 2, 41), ((20, 80), 1, 41), ((20, 81), 0, 41), ((20, 82), 0, 83),
   ((20, 83), 2, 43), ((20, 84), 1, 43), ((20, 85), 0, 43), ((20, 86), 0, 29), ((20, 87), 1, 89),
   ((20, 88), 0, 89), ((20, 89), 2, 23), ((20, 90), 1, 23), ((20, 91), 0, 23), ((20, 92), 0, 31),
   ((20, 93), 0, 47), ((20, 94), 2, 97), ((20, 95), 1, 97), ((20, 96), 0, 97), ((20, 97), 3, 101),
   ((20, 98), 2, 101), ((20, 99), 1, 101), ((20, 100), 0, 101), ((20, 101), 1, 103),
   ((20, 102), 0, 103), ((20, 103), 2, 53), ((20, 104), 1, 53), ((20, 105), 0, 53),
   ((20, 106), 0, 107), ((20, 107), 1, 109), ((20, 108), 0, 109), ((20, 109), 1, 37),
   ((20, 110), 0, 37), ((20, 111), 1, 113), ((20, 112), 0, 113), ((20, 113), 1, 23),
   ((20, 114), 0, 23), ((20, 115), 0, 29), ((20, 116), 1, 59), ((20, 117), 0, 59),
   ((20, 118), 3, 61), ((20, 119), 2, 61), ((20, 120), 1, 61), ((20, 121), 0, 61),
   ((20, 122), 0, 41), ((20, 123), 0, 31), ((20, 124), 2, 127), ((20, 125), 1, 127),
   ((20, 126), 0, 127), ((20, 127), 1, 43), ((20, 128), 0, 43), ((20, 129), 1, 131),
   ((20, 130), 0, 131), ((20, 131), 2, 67), ((20, 132), 1, 67), ((20, 133), 0, 67),
   ((20, 134), 2, 137), ((20, 135), 1, 137), ((20, 136), 0, 137), ((20, 137), 0, 23),
   ((20, 138), 0, 139), ((20, 139), 1, 47), ((20, 140), 0, 47), ((20, 141), 0, 71),
   ((20, 142), 2, 29), ((20, 143), 1, 29), ((20, 144), 0, 29), ((20, 145), 0, 73),
   ((20, 146), 1, 37), ((20, 147), 0, 37), ((20, 148), 0, 149), ((20, 149), 1, 151),
   ((20, 150), 0, 151), ((20, 151), 3, 31), ((20, 152), 2, 31), ((20, 153), 1, 31),
   ((20, 154), 0, 31), ((20, 155), 1, 157), ((20, 156), 0, 157), ((20, 157), 0, 79),
   ((20, 158), 0, 53), ((20, 159), 1, 23), ((20, 160), 0, 23), ((20, 161), 1, 163),
   ((20, 162), 0, 163), ((20, 163), 0, 41), ((20, 164), 1, 83), ((20, 165), 0, 83),
   ((20, 166), 0, 167), ((20, 167), 4, 43), ((20, 168), 3, 43), ((20, 169), 2, 43),
   ((20, 170), 1, 43), ((20, 171), 0, 43), ((20, 172), 0, 173), ((20, 173), 0, 29),
   ((20, 174), 2, 59), ((20, 175), 1, 59), ((20, 176), 0, 59), ((20, 177), 0, 89),
   ((20, 178), 0, 179), ((20, 179), 1, 181), ((20, 180), 0, 181), ((20, 181), 1, 61),
   ((20, 182), 0, 61), ((20, 183), 0, 23), ((20, 184), 0, 37), ((20, 185), 0, 31),
   ((20, 186), 1, 47), ((20, 187), 0, 47), ((20, 188), 2, 191), ((20, 189), 1, 191),
   ((20, 190), 0, 191), ((20, 191), 1, 193), ((20, 192), 0, 193), ((20, 193), 0, 97),
   ((20, 194), 2, 197), ((20, 195), 1, 197), ((20, 196), 0, 197), ((20, 197), 1, 199),
   ((20, 198), 0, 199), ((20, 199), 1, 67), ((21, 0), 0, 0), ((21, 1), 0, 0), ((21, 2), 0, 0),
   ((21, 3), 0, 0), ((21, 4), 0, 0), ((21, 5), 0, 0), ((21, 6), 0, 0), ((21, 7), 0, 0),
   ((21, 8), 0, 0), ((21, 9), 0, 0), ((21, 10), 0, 0), ((21, 11), 0, 0), ((21, 12), 0, 0),
   ((21, 13), 0, 0), ((21, 14), 0, 0), ((21, 15), 0, 0), ((21, 16), 0, 0), ((21, 17), 0, 0),
   ((21, 18), 0, 0), ((21, 19), 0, 0), ((21, 20), 0, 0), ((21, 21), 0, 0), ((21, 22), 0, 23),
   ((21, 23), 5, 29), ((21, 24), 4, 29), ((21, 25), 3, 29), ((21, 26), 2, 29), ((21, 27), 1, 29),
   ((21, 28), 0, 29), ((21, 29), 1, 31), ((21, 30), 0, 31), ((21, 31), 5, 37), ((21, 32), 4, 37),
   ((21, 33), 3, 37), ((21, 34), 2, 37), ((21, 35), 1, 37), ((21, 36), 0, 37), ((21, 37), 3, 41),
   ((21, 38), 2, 41), ((21, 39), 1, 41), ((21, 40), 0, 41), ((21, 41), 1, 43), ((21, 42), 0, 43),
   ((21, 43), 2, 23), ((21, 44), 1, 23), ((21, 45), 0, 23), ((21, 46), 0, 47), ((21, 47), 5, 53),
   ((21, 48), 4, 53), ((21, 49), 3, 53), ((21, 50), 2, 53), ((21, 51), 1, 53), ((21, 52), 0, 53),
   ((21, 53), 4, 29), ((21, 54), 3, 29), ((21, 55), 2, 29), ((21, 56), 1, 29), ((21, 57), 0, 29),
   ((21, 58), 0, 59), ((21, 59), 1, 61), ((21, 60), 0, 61), ((21, 61), 0, 31), ((21, 62), 4, 67),
   ((21, 63), 3, 67), ((21, 64), 2, 67), ((21, 65), 1, 67), ((21, 66), 0, 67), ((21, 67), 1, 23),
   ((21, 68), 0, 23), ((21, 69), 1, 71), ((21, 70), 0, 71), ((21, 71), 1, 73), ((21, 72), 0, 73),
   ((21, 73), 0, 37), ((21, 74), 4, 79), ((21, 75), 3, 79), ((21, 76), 2, 79), ((21, 77), 1, 79),
   ((21, 78), 0, 79), ((21, 79), 2, 41), ((21, 80), 1, 41), ((21, 81), 0, 41), ((21, 82), 0, 83),
   ((21, 83), 2, 43), ((21, 84), 1, 43), ((21, 85), 0, 43), ((21, 86), 0, 29), ((21, 87), 1, 89),
   ((21, 88), 0, 89), ((21, 89), 2, 23), ((21, 90), 1, 23), ((21, 91), 0, 23), ((21, 92), 0, 31),
   ((21, 93), 0, 47), ((21, 94), 2, 97), ((21, 95), 1, 97), ((21, 96), 0, 97), ((21, 97), 3, 101),
   ((21, 98), 2, 101), ((21, 99), 1, 101), ((21, 100), 0, 101), ((21, 101), 1, 103),
   ((21, 102), 0, 103), ((21, 103), 2, 53), ((21, 104), 1, 53), ((21, 105), 0, 53),
   ((21, 106), 0, 107), ((21, 107), 1, 109), ((21, 108), 0, 109), ((21, 109), 1, 37),
   ((21, 110), 0, 37), ((21, 111), 1, 113), ((21, 112), 0, 113), ((21, 113), 1, 23),
   ((21, 114), 0, 23), ((21, 115), 0, 29), ((21, 116), 1, 59), ((21, 117), 0, 59),
   ((21, 118), 3, 61), ((21, 119), 2, 61), ((21, 120), 1, 61), ((21, 121), 0, 61),
   ((21, 122), 0, 41), ((21, 123), 0, 31), ((21, 124), 2, 127), ((21, 125), 1, 127),
   ((21, 126), 0, 127), ((21, 127), 1, 43), ((21, 128), 0, 43), ((21, 129), 1, 131),
   ((21, 130), 0, 131), ((21, 131), 2, 67), ((21, 132), 1, 67), ((21, 133), 0, 67),
   ((21, 134), 2, 137), ((21, 135), 1, 137), ((21, 136), 0, 137), ((21, 137), 0, 23),
   ((21, 138), 0, 139), ((21, 139), 1, 47), ((21, 140), 0, 47), ((21, 141), 0, 71),
   ((21, 142), 2, 29), ((21, 143), 1, 29), ((21, 144), 0, 29), ((21, 145), 0, 73),
   ((21, 146), 1, 37), ((21, 147), 0, 37), ((21, 148), 0, 149), ((21, 149), 1, 151),
   ((21, 150), 0, 151), ((21, 151), 3, 31), ((21, 152), 2, 31), ((21, 153), 1, 31),
   ((21, 154), 0, 31), ((21, 155), 1, 157), ((21, 156), 0, 157), ((21, 157), 0, 79),
   ((21, 158), 0, 53), ((21, 159), 1, 23), ((21, 160), 0, 23), ((21, 161), 1, 163),
   ((21, 162), 0, 163), ((21, 163), 0, 41), ((21, 164), 1, 83), ((21, 165), 0, 83),
   ((21, 166), 0, 167), ((21, 167), 4, 43), ((21, 168), 3, 43), ((21, 169), 2, 43),
   ((21, 170), 1, 43), ((21, 171), 0, 43), ((21, 172), 0, 173), ((21, 173), 0, 29),
   ((21, 174), 2, 59), ((21, 175), 1, 59), ((21, 176), 0, 59), ((21, 177), 0, 89),
   ((21, 178), 0, 179), ((21, 179), 1, 181), ((21, 180), 0, 181), ((21, 181), 1, 61),
   ((21, 182), 0, 61), ((21, 183), 0, 23), ((21, 184), 0, 37), ((21, 185), 0, 31),
   ((21, 186), 1, 47), ((21, 187), 0, 47), ((21, 188), 2, 191), ((21, 189), 1, 191),
   ((21, 190), 0, 191), ((21, 191), 1, 193), ((21, 192), 0, 193), ((21, 193), 0, 97),
   ((21, 194), 2, 197), ((21, 195), 1, 197), ((21, 196), 0, 197), ((21, 197), 1, 199),
   ((21, 198), 0, 199), ((21, 199), 1, 67), ((22, 0), 0, 0), ((22, 1), 0, 0), ((22, 2), 0, 0),
   ((22, 3), 0, 0), ((22, 4), 0, 0), ((22, 5), 0, 0), ((22, 6), 0, 0), ((22, 7), 0, 0),
   ((22, 8), 0, 0), ((22, 9), 0, 0), ((22, 10), 0, 0), ((22, 11), 0, 0), ((22, 12), 0, 0),
   ((22, 13), 0, 0), ((22, 14), 0, 0), ((22, 15), 0, 0), ((22, 16), 0, 0), ((22, 17), 0, 0),
   ((22, 18), 0, 0), ((22, 19), 0, 0), ((22, 20), 0, 0), ((22, 21), 0, 0), ((22, 22), 0, 0),
   ((22, 23), 5, 29), ((22, 24), 4, 29), ((22, 25), 3, 29), ((22, 26), 2, 29), ((22, 27), 1, 29),
   ((22, 28), 0, 29), ((22, 29), 1, 31), ((22, 30), 0, 31), ((22, 31), 5, 37), ((22, 32), 4, 37),
   ((22, 33), 3, 37), ((22, 34), 2, 37), ((22, 35), 1, 37), ((22, 36), 0, 37), ((22, 37), 3, 41),
   ((22, 38), 2, 41), ((22, 39), 1, 41), ((22, 40), 0, 41), ((22, 41), 1, 43), ((22, 42), 0, 43),
   ((22, 43), 2, 23), ((22, 44), 1, 23), ((22, 45), 0, 23), ((22, 46), 0, 47), ((22, 47), 5, 53),
   ((22, 48), 4, 53), ((22, 49), 3, 53), ((22, 50), 2, 53), ((22, 51), 1, 53), ((22, 52), 0, 53),
   ((22, 53), 4, 29), ((22, 54), 3, 29), ((22, 55), 2, 29), ((22, 56), 1, 29), ((22, 57), 0, 29),
   ((22, 58), 0, 59), ((22, 59), 1, 61), ((22, 60), 0, 61), ((22, 61), 0, 31), ((22, 62), 4, 67),
   ((22, 63), 3, 67), ((22, 64), 2, 67), ((22, 65), 1, 67), ((22, 66), 0, 67), ((22, 67), 1, 23),
   ((22, 68), 0, 23), ((22, 69), 1, 71), ((22, 70), 0, 71), ((22, 71), 1, 73), ((22, 72), 0, 73),
   ((22, 73), 0, 37), ((22, 74), 4, 79), ((22, 75), 3, 79), ((22, 76), 2, 79), ((22, 77), 1, 79),
   ((22, 78), 0, 79), ((22, 79), 2, 41), ((22, 80), 1, 41), ((22, 81), 0, 41), ((22, 82), 0, 83),
   ((22, 83), 2, 43), ((22, 84), 1, 43), ((22, 85), 0, 43), ((22, 86), 0, 29), ((22, 87), 1, 89),
   ((22, 88), 0, 89), ((22, 89), 2, 23), ((22, 90), 1, 23), ((22, 91), 0, 23), ((22, 92), 0, 31),
   ((22, 93), 0, 47), ((22, 94), 2, 97), ((22, 95), 1, 97), ((22, 96), 0, 97), ((22, 97), 3, 101),
   ((22, 98), 2, 101), ((22, 99), 1, 101), ((22, 100), 0, 101), ((22, 101), 1, 103),
   ((22, 102), 0, 103), ((22, 103), 2, 53), ((22, 104), 1, 53), ((22, 105), 0, 53),
   ((22, 106), 0, 107), ((22, 107), 1, 109), ((22, 108), 0, 109), ((22, 109), 1, 37),
   ((22, 110), 0, 37), ((22, 111), 1, 113), ((22, 112), 0, 113), ((22, 113), 1, 23),
   ((22, 114), 0, 23), ((22, 115), 0, 29), ((22, 116), 1, 59), ((22, 117), 0, 59),
   ((22, 118), 3, 61), ((22, 119), 2, 61), ((22, 120), 1, 61), ((22, 121), 0, 61),
   ((22, 122), 0, 41), ((22, 123), 0, 31), ((22, 124), 2, 127), ((22, 125), 1, 127),
   ((22, 126), 0, 127), ((22, 127), 1, 43), ((22, 128), 0, 43), ((22, 129), 1, 131),
   ((22, 130), 0, 131), ((22, 131), 2, 67), ((22, 132), 1, 67), ((22, 133), 0, 67),
   ((22, 134), 2, 137), ((22, 135), 1, 137), ((22, 136), 0, 137), ((22, 137), 0, 23),
   ((22, 138), 0, 139), ((22, 139), 1, 47), ((22, 140), 0, 47), ((22, 141), 0, 71),
   ((22, 142), 2, 29), ((22, 143), 1, 29), ((22, 144), 0, 29), ((22, 145), 0, 73),
   ((22, 146), 1, 37), ((22, 147), 0, 37), ((22, 148), 0, 149), ((22, 149), 1, 151),
   ((22, 150), 0, 151), ((22, 151), 3, 31), ((22, 152), 2, 31), ((22, 153), 1, 31),
   ((22, 154), 0, 31), ((22, 155), 1, 157), ((22, 156), 0, 157), ((22, 157), 0, 79),
   ((22, 158), 0, 53), ((22, 159), 1, 23), ((22, 160), 0, 23), ((22, 161), 1, 163),
   ((22, 162), 0, 163), ((22, 163), 0, 41), ((22, 164), 1, 83), ((22, 165), 0, 83),
   ((22, 166), 0, 167), ((22, 167), 4, 43), ((22, 168), 3, 43), ((22, 169), 2, 43),
   ((22, 170), 1, 43), ((22, 171), 0, 43), ((22, 172), 0, 173), ((22, 173), 0, 29),
   ((22, 174), 2, 59), ((22, 175), 1, 59), ((22, 176), 0, 59), ((22, 177), 0, 89),
   ((22, 178), 0, 179), ((22, 179), 1, 181), ((22, 180), 0, 181), ((22, 181), 1, 61),
   ((22, 182), 0, 61), ((22, 183), 0, 23), ((22, 184), 0, 37), ((22, 185), 0, 31),
   ((22, 186), 1, 47), ((22, 187), 0, 47), ((22, 188), 2, 191), ((22, 189), 1, 191),
   ((22, 190), 0, 191), ((22, 191), 1, 193), ((22, 192), 0, 193), ((22, 193), 0, 97),
   ((22, 194), 2, 197), ((22, 195), 1, 197), ((22, 196), 0, 197), ((22, 197), 1, 199),
   ((22, 198), 0, 199), ((22, 199), 1, 67), ((23, 0), 0, 0), ((23, 1), 0, 0), ((23, 2), 0, 0),
   ((23, 3), 0, 0), ((23, 4), 0, 0), ((23, 5), 0, 0), ((23, 6), 0, 0), ((23, 7), 0, 0),
   ((23, 8), 0, 0), ((23, 9), 0, 0), ((23, 10), 0, 0), ((23, 11), 0, 0), ((23, 12), 0, 0),
   ((23, 13), 0, 0), ((23, 14), 0, 0), ((23, 15), 0, 0), ((23, 16), 0, 0), ((23, 17), 0, 0),
   ((23, 18), 0, 0), ((23, 19), 0, 0), ((23, 20), 0, 0), ((23, 21), 0, 0), ((23, 22), 0, 0),
   ((23, 23), 0, 0), ((23, 24), 4, 29), ((23, 25), 3, 29), ((23, 26), 2, 29), ((23, 27), 1, 29),
   ((23, 28), 0, 29), ((23, 29), 1, 31), ((23, 30), 0, 31), ((23, 31), 5, 37), ((23, 32), 4, 37),
   ((23, 33), 3, 37), ((23, 34), 2, 37), ((23, 35), 1, 37), ((23, 36), 0, 37), ((23, 37), 3, 41),
   ((23, 38), 2, 41), ((23, 39), 1, 41), ((23, 40), 0, 41), ((23, 41), 1, 43), ((23, 42), 0, 43),
   ((23, 43), 3, 47), ((23, 44), 2, 47), ((23, 45), 1, 47), ((23, 46), 0, 47), ((23, 47), 5, 53),
   ((23, 48), 4, 53), ((23, 49), 3, 53), ((23, 50), 2, 53), ((23, 51), 1, 53), ((23, 52), 0, 53),
   ((23, 53), 4, 29), ((23, 54), 3, 29), ((23, 55), 2, 29), ((23, 56), 1, 29), ((23, 57), 0, 29),
   ((23, 58), 0, 59), ((23, 59), 1, 61), ((23, 60), 0, 61), ((23, 61), 0, 31), ((23, 62), 4, 67),
   ((23, 63), 3, 67), ((23, 64), 2, 67), ((23, 65), 1, 67), ((23, 66), 0, 67), ((23, 67), 3, 71),
   ((23, 68), 2, 71), ((23, 69), 1, 71), ((23, 70), 0, 71), ((23, 71), 1, 73), ((23, 72), 0, 73),
   ((23, 73), 0, 37), ((23, 74), 4, 79), ((23, 75), 3, 79), ((23, 76), 2, 79), ((23, 77), 1, 79),
   ((23, 78), 0, 79), ((23, 79), 2, 41), ((23, 80), 1, 41), ((23, 81), 0, 41), ((23, 82), 0, 83),
   ((23, 83), 2, 43), ((23, 84), 1, 43), ((23, 85), 0, 43), ((23, 86), 0, 29), ((23, 87), 1, 89),
   ((23, 88), 0, 89), ((23, 89), 3, 31), ((23, 90), 2, 31), ((23, 91), 1, 31), ((23, 92), 0, 31),
   ((23, 93), 0, 47), ((23, 94), 2, 97), ((23, 95), 1, 97), ((23, 96), 0, 97), ((23, 97), 3, 101),
   ((23, 98), 2, 101), ((23, 99), 1, 101), ((23, 100), 0, 101), ((23, 101), 1, 103),
   ((23, 102), 0, 103), ((23, 103), 2, 53), ((23, 104), 1, 53), ((23, 105), 0, 53),
   ((23, 106), 0, 107), ((23, 107), 1, 109), ((23, 108), 0, 109), ((23, 109), 1, 37),
   ((23, 110), 0, 37), ((23, 111), 1, 113), ((23, 112), 0, 113), ((23, 113), 2, 29),
   ((23, 114), 1, 29), ((23, 115), 0, 29), ((23, 116), 1, 59), ((23, 117), 0, 59),
   ((23, 118), 3, 61), ((23, 119), 2, 61), ((23, 120), 1, 61), ((23, 121), 0, 61),
   ((23, 122), 0, 41), ((23, 123), 0, 31), ((23, 124), 2, 127), ((23, 125), 1, 127),
   ((23, 126), 0, 127), ((23, 127), 1, 43), ((23, 128), 0, 43), ((23, 129), 1, 131),
   ((23, 130), 0, 131), ((23, 131), 2, 67), ((23, 132), 1, 67), ((23, 133), 0, 67),
   ((23, 134), 2, 137), ((23, 135), 1, 137), ((23, 136), 0, 137), ((23, 137), 1, 139),
   ((23, 138), 0, 139), ((23, 139), 1, 47), ((23, 140), 0, 47), ((23, 141), 0, 71),
   ((23, 142), 2, 29), ((23, 143), 1, 29), ((23, 144), 0, 29), ((23, 145), 0, 73),
   ((23, 146), 1, 37), ((23, 147), 0, 37), ((23, 148), 0, 149), ((23, 149), 1, 151),
   ((23, 150), 0, 151), ((23, 151), 3, 31), ((23, 152), 2, 31), ((23, 153), 1, 31),
   ((23, 154), 0, 31), ((23, 155), 1, 157), ((23, 156), 0, 157), ((23, 157), 0, 79),
   ((23, 158), 0, 53), ((23, 159), 3, 163), ((23, 160), 2, 163), ((23, 161), 1, 163),
   ((23, 162), 0, 163), ((23, 163), 0, 41), ((23, 164), 1, 83), ((23, 165), 0, 83),
   ((23, 166), 0, 167), ((23, 167), 4, 43), ((23, 168), 3, 43), ((23, 169), 2, 43),
   ((23, 170), 1, 43), ((23, 171), 0, 43), ((23, 172), 0, 173), ((23, 173), 0, 29),
   ((23, 174), 2, 59), ((23, 175), 1, 59), ((23, 176), 0, 59), ((23, 177), 0, 89),
   ((23, 178), 0, 179), ((23, 179), 1, 181), ((23, 180), 0, 181), ((23, 181), 1, 61),
   ((23, 182), 0, 61), ((23, 183), 1, 37), ((23, 184), 0, 37), ((23, 185), 0, 31),
   ((23, 186), 1, 47), ((23, 187), 0, 47), ((23, 188), 2, 191), ((23, 189), 1, 191),
   ((23, 190), 0, 191), ((23, 191), 1, 193), ((23, 192), 0, 193), ((23, 193), 0, 97),
   ((23, 194), 2, 197), ((23, 195), 1, 197), ((23, 196), 0, 197), ((23, 197), 1, 199),
   ((23, 198), 0, 199), ((23, 199), 1, 67), ((24, 0), 0, 0), ((24, 1), 0, 0), ((24, 2), 0, 0),
   ((24, 3), 0, 0), ((24, 4), 0, 0), ((24, 5), 0, 0), ((24, 6), 0, 0), ((24, 7), 0, 0),
   ((24, 8), 0, 0), ((24, 9), 0, 0), ((24, 10), 0, 0), ((24, 11), 0, 0), ((24, 12), 0, 0),
   ((24, 13), 0, 0), ((24, 14), 0, 0), ((24, 15), 0, 0), ((24, 16), 0, 0), ((24, 17), 0, 0),
   ((24, 18), 0, 0), ((24, 19), 0, 0), ((24, 20), 0, 0), ((24, 21), 0, 0), ((24, 22), 0, 0),
   ((24, 23), 0, 0), ((24, 24), 0, 0), ((24, 25), 3, 29), ((24, 26), 2, 29), ((24, 27), 1, 29),
   ((24, 28), 0, 29), ((24, 29), 1, 31), ((24, 30), 0, 31), ((24, 31), 5, 37), ((24, 32), 4, 37),
   ((24, 33), 3, 37), ((24, 34), 2, 37), ((24, 35), 1, 37), ((24, 36), 0, 37), ((24, 37), 3, 41),
   ((24, 38), 2, 41), ((24, 39), 1, 41), ((24, 40), 0, 41), ((24, 41), 1, 43), ((24, 42), 0, 43),
   ((24, 43), 3, 47), ((24, 44), 2, 47), ((24, 45), 1, 47), ((24, 46), 0, 47), ((24, 47), 5, 53),
   ((24, 48), 4, 53), ((24, 49), 3, 53), ((24, 50), 2, 53), ((24, 51), 1, 53), ((24, 52), 0, 53),
   ((24, 53), 4, 29), ((24, 54), 3, 29), ((24, 55), 2, 29), ((24, 56), 1, 29), ((24, 57), 0, 29),
   ((24, 58), 0, 59), ((24, 59), 1, 61), ((24, 60), 0, 61), ((24, 61), 0, 31), ((24, 62), 4, 67),
   ((24, 63), 3, 67), ((24, 64), 2, 67), ((24, 65), 1, 67), ((24, 66), 0, 67), ((24, 67), 3, 71),
   ((24, 68), 2, 71), ((24, 69), 1, 71), ((24, 70), 0, 71), ((24, 71), 1, 73), ((24, 72), 0, 73),
   ((24, 73), 0, 37), ((24, 74), 4, 79), ((24, 75), 3, 79), ((24, 76), 2, 79), ((24, 77), 1, 79),
   ((24, 78), 0, 79), ((24, 79), 2, 41), ((24, 80), 1, 41), ((24, 81), 0, 41), ((24, 82), 0, 83),
   ((24, 83), 2, 43), ((24, 84), 1, 43), ((24, 85), 0, 43), ((24, 86), 0, 29), ((24, 87), 1, 89),
   ((24, 88), 0, 89), ((24, 89), 3, 31), ((24, 90), 2, 31), ((24, 91), 1, 31), ((24, 92), 0, 31),
   ((24, 93), 0, 47), ((24, 94), 2, 97), ((24, 95), 1, 97), ((24, 96), 0, 97), ((24, 97), 3, 101),
   ((24, 98), 2, 101), ((24, 99), 1, 101), ((24, 100), 0, 101), ((24, 101), 1, 103),
   ((24, 102), 0, 103), ((24, 103), 2, 53), ((24, 104), 1, 53), ((24, 105), 0, 53),
   ((24, 106), 0, 107), ((24, 107), 1, 109), ((24, 108), 0, 109), ((24, 109), 1, 37),
   ((24, 110), 0, 37), ((24, 111), 1, 113), ((24, 112), 0, 113), ((24, 113), 2, 29),
   ((24, 114), 1, 29), ((24, 115), 0, 29), ((24, 116), 1, 59), ((24, 117), 0, 59),
   ((24, 118), 3, 61), ((24, 119), 2, 61), ((24, 120), 1, 61), ((24, 121), 0, 61),
   ((24, 122), 0, 41), ((24, 123), 0, 31), ((24, 124), 2, 127), ((24, 125), 1, 127),
   ((24, 126), 0, 127), ((24, 127), 1, 43), ((24, 128), 0, 43), ((24, 129), 1, 131),
   ((24, 130), 0, 131), ((24, 131), 2, 67), ((24, 132), 1, 67), ((24, 133), 0, 67),
   ((24, 134), 2, 137), ((24, 135), 1, 137), ((24, 136), 0, 137), ((24, 137), 1, 139),
   ((24, 138), 0, 139), ((24, 139), 1, 47), ((24, 140), 0, 47), ((24, 141), 0, 71),
   ((24, 142), 2, 29), ((24, 143), 1, 29), ((24, 144), 0, 29), ((24, 145), 0, 73),
   ((24, 146), 1, 37), ((24, 147), 0, 37), ((24, 148), 0, 149), ((24, 149), 1, 151),
   ((24, 150), 0, 151), ((24, 151), 3, 31), ((24, 152), 2, 31), ((24, 153), 1, 31),
   ((24, 154), 0, 31), ((24, 155), 1, 157), ((24, 156), 0, 157), ((24, 157), 0, 79),
   ((24, 158), 0, 53), ((24, 159), 3, 163), ((24, 160), 2, 163), ((24, 161), 1, 163),
   ((24, 162), 0, 163), ((24, 163), 0, 41), ((24, 164), 1, 83), ((24, 165), 0, 83),
   ((24, 166), 0, 167), ((24, 167), 4, 43), ((24, 168), 3, 43), ((24, 169), 2, 43),
   ((24, 170), 1, 43), ((24, 171), 0, 43), ((24, 172), 0, 173), ((24, 173), 0, 29),
   ((24, 174), 2, 59), ((24, 175), 1, 59), ((24, 176), 0, 59), ((24, 177), 0, 89),
   ((24, 178), 0, 179), ((24, 179), 1, 181), ((24, 180), 0, 181), ((24, 181), 1, 61),
   ((24, 182), 0, 61), ((24, 183), 1, 37), ((24, 184), 0, 37), ((24, 185), 0, 31),
   ((24, 186), 1, 47), ((24, 187), 0, 47), ((24, 188), 2, 191), ((24, 189), 1, 191),
   ((24, 190), 0, 191), ((24, 191), 1, 193), ((24, 192), 0, 193), ((24, 193), 0, 97),
   ((24, 194), 2, 197), ((24, 195), 1, 197), ((24, 196), 0, 197), ((24, 197), 1, 199),
   ((24, 198), 0, 199), ((24, 199), 1, 67), ((25, 0), 0, 0), ((25, 1), 0, 0), ((25, 2), 0, 0),
   ((25, 3), 0, 0), ((25, 4), 0, 0), ((25, 5), 0, 0), ((25, 6), 0, 0), ((25, 7), 0, 0),
   ((25, 8), 0, 0), ((25, 9), 0, 0), ((25, 10), 0, 0), ((25, 11), 0, 0), ((25, 12), 0, 0),
   ((25, 13), 0, 0), ((25, 14), 0, 0), ((25, 15), 0, 0), ((25, 16), 0, 0), ((25, 17), 0, 0),
   ((25, 18), 0, 0), ((25, 19), 0, 0), ((25, 20), 0, 0), ((25, 21), 0, 0), ((25, 22), 0, 0),
   ((25, 23), 0, 0), ((25, 24), 0, 0), ((25, 25), 0, 0), ((25, 26), 2, 29), ((25, 27), 1, 29),
   ((25, 28), 0, 29), ((25, 29), 1, 31), ((25, 30), 0, 31), ((25, 31), 5, 37), ((25, 32), 4, 37),
   ((25, 33), 3, 37), ((25, 34), 2, 37), ((25, 35), 1, 37), ((25, 36), 0, 37), ((25, 37), 3, 41),
   ((25, 38), 2, 41), ((25, 39), 1, 41), ((25, 40), 0, 41), ((25, 41), 1, 43), ((25, 42), 0, 43),
   ((25, 43), 3, 47), ((25, 44), 2, 47), ((25, 45), 1, 47), ((25, 46), 0, 47), ((25, 47), 5, 53),
   ((25, 48), 4, 53), ((25, 49), 3, 53), ((25, 50), 2, 53), ((25, 51), 1, 53), ((25, 52), 0, 53),
   ((25, 53), 4, 29), ((25, 54), 3, 29), ((25, 55), 2, 29), ((25, 56), 1, 29), ((25, 57), 0, 29),
   ((25, 58), 0, 59), ((25, 59), 1, 61), ((25, 60), 0, 61), ((25, 61), 0, 31), ((25, 62), 4, 67),
   ((25, 63), 3, 67), ((25, 64), 2, 67), ((25, 65), 1, 67), ((25, 66), 0, 67), ((25, 67), 3, 71),
   ((25, 68), 2, 71), ((25, 69), 1, 71), ((25, 70), 0, 71), ((25, 71), 1, 73), ((25, 72), 0, 73),
   ((25, 73), 0, 37), ((25, 74), 4, 79), ((25, 75), 3, 79), ((25, 76), 2, 79), ((25, 77), 1, 79),
   ((25, 78), 0, 79), ((25, 79), 2, 41), ((25, 80), 1, 41), ((25, 81), 0, 41), ((25, 82), 0, 83),
   ((25, 83), 2, 43), ((25, 84), 1, 43), ((25, 85), 0, 43), ((25, 86), 0, 29), ((25, 87), 1, 89),
   ((25, 88), 0, 89), ((25, 89), 3, 31), ((25, 90), 2, 31), ((25, 91), 1, 31), ((25, 92), 0, 31),
   ((25, 93), 0, 47), ((25, 94), 2, 97), ((25, 95), 1, 97), ((25, 96), 0, 97), ((25, 97), 3, 101),
   ((25, 98), 2, 101), ((25, 99), 1, 101), ((25, 100), 0, 101), ((25, 101), 1, 103),
   ((25, 102), 0, 103), ((25, 103), 2, 53), ((25, 104), 1, 53), ((25, 105), 0, 53),
   ((25, 106), 0, 107), ((25, 107), 1, 109), ((25, 108), 0, 109), ((25, 109), 1, 37),
   ((25, 110), 0, 37), ((25, 111), 1, 113), ((25, 112), 0, 113), ((25, 113), 2, 29),
   ((25, 114), 1, 29), ((25, 115), 0, 29), ((25, 116), 1, 59), ((25, 117), 0, 59),
   ((25, 118), 3, 61), ((25, 119), 2, 61), ((25, 120), 1, 61), ((25, 121), 0, 61),
   ((25, 122), 0, 41), ((25, 123), 0, 31), ((25, 124), 2, 127), ((25, 125), 1, 127),
   ((25, 126), 0, 127), ((25, 127), 1, 43), ((25, 128), 0, 43), ((25, 129), 1, 131),
   ((25, 130), 0, 131), ((25, 131), 2, 67), ((25, 132), 1, 67), ((25, 133), 0, 67),
   ((25, 134), 2, 137), ((25, 135), 1, 137), ((25, 136), 0, 137), ((25, 137), 1, 139),
   ((25, 138), 0, 139), ((25, 139), 1, 47), ((25, 140), 0, 47), ((25, 141), 0, 71),
   ((25, 142), 2, 29), ((25, 143), 1, 29), ((25, 144), 0, 29), ((25, 145), 0, 73),
   ((25, 146), 1, 37), ((25, 147), 0, 37), ((25, 148), 0, 149), ((25, 149), 1, 151),
   ((25, 150), 0, 151), ((25, 151), 3, 31), ((25, 152), 2, 31), ((25, 153), 1, 31),
   ((25, 154), 0, 31), ((25, 155), 1, 157), ((25, 156), 0, 157), ((25, 157), 0, 79),
   ((25, 158), 0, 53), ((25, 159), 3, 163), ((25, 160), 2, 163), ((25, 161), 1, 163),
   ((25, 162), 0, 163), ((25, 163), 0, 41), ((25, 164), 1, 83), ((25, 165), 0, 83),
   ((25, 166), 0, 167), ((25, 167), 4, 43), ((25, 168), 3, 43), ((25, 169), 2, 43),
   ((25, 170), 1, 43), ((25, 171), 0, 43), ((25, 172), 0, 173), ((25, 173), 0, 29),
   ((25, 174), 2, 59), ((25, 175), 1, 59), ((25, 176), 0, 59), ((25, 177), 0, 89),
   ((25, 178), 0, 179), ((25, 179), 1, 181), ((25, 180), 0, 181), ((25, 181), 1, 61),
   ((25, 182), 0, 61), ((25, 183), 1, 37), ((25, 184), 0, 37), ((25, 185), 0, 31),
   ((25, 186), 1, 47), ((25, 187), 0, 47), ((25, 188), 2, 191), ((25, 189), 1, 191),
   ((25, 190), 0, 191), ((25, 191), 1, 193), ((25, 192), 0, 193), ((25, 193), 0, 97),
   ((25, 194), 2, 197), ((25, 195), 1, 197), ((25, 196), 0, 197), ((25, 197), 1, 199),
   ((25, 198), 0, 199), ((25, 199), 1, 67)]

set_option maxRecDepth 100000 in
/-- The table covers every pair `(k, n)` with `k < 26` and `n < 200`. -/
theorem smallTable_keys :
    smallTable.map Prod.fst =
      (List.range 26).flatMap (fun k => (List.range 200).map (fun n => (k, n))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Every relevant entry of the table is a valid witness. -/
theorem smallTable_spec : ∀ e ∈ smallTable, 0 < e.1.1 → e.1.1 < e.1.2 →
    e.2.2 ∈ smallPrimes ∧ e.1.1 < e.2.2 ∧ e.2.1 < e.1.1 ∧
      e.2.2 ∣ (e.1.2 + 1 + e.2.1) := by
  decide +kernel

theorem small_cases : ∀ k ∈ Finset.range 26, ∀ n ∈ Finset.range 200, 0 < k → k < n →
    ∃ i ∈ Finset.range k, ∃ p ∈ smallPrimes, k < p ∧ p ∣ (n + 1 + i) := by
  intro k hk n hn hk0 hkn
  have hmem : (k, n) ∈ smallTable.map Prod.fst := by
    rw [smallTable_keys]
    simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨k, Finset.mem_range.1 hk, n, Finset.mem_range.1 hn, rfl⟩
  obtain ⟨e, he, hek⟩ := List.mem_map.1 hmem
  have hk1 : e.1.1 = k := by rw [hek]
  have hk2 : e.1.2 = n := by rw [hek]
  obtain ⟨h1, h2, h3, h4⟩ :=
    smallTable_spec e he (by rw [hk1]; exact hk0) (by rw [hk1, hk2]; exact hkn)
  rw [hk1] at h2 h3
  rw [hk2] at h4
  exact ⟨e.2.1, Finset.mem_range.2 h3, e.2.2, h1, h2, h4⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000 in
theorem small_pow_lt : ∀ k ∈ Finset.range 26, 0 < k → k ^ k < 200 ^ (k - piCount k) := by
  decide

/-! ### The theorem -/

/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/
theorem sylvester_schur (n k : ℕ) (h : k < n) (hk : 0 < k) :
    ∃ i ∈ Finset.range k, ∃ p, p.Prime ∧ k < p ∧ p ∣ (n + 1 + i) := by
  by_contra hcon0
  have hcon : ∀ i ∈ Finset.range k, ∀ p : ℕ, p.Prime → k < p → ¬ p ∣ (n + 1 + i) :=
    fun i hi p hp hkp hpd => hcon0 ⟨i, hi, p, hp, hkp, hpd⟩
  set N := n + k with hNdef
  have hpi : piCount k ≤ k := piCount_le_self k
  have hNpos : 0 < N := by omega
  -- there is no prime in the interval `(n, n+k]`
  have hnoprime : ∀ p : ℕ, p.Prime → n < p → p ≤ n + k → False := by
    intro p hp h1 h2
    refine hcon (p - n - 1) (Finset.mem_range.2 (by omega)) p hp (by omega) ?_
    have : n + 1 + (p - n - 1) = p := by omega
    rw [this]
  -- every prime factor of the binomial coefficient is at most `k`
  have hH : ∀ p : ℕ, p.Prime → p ∣ N.choose k → p ≤ k := by
    intro p hp hdvd
    by_contra hpk
    rw [not_le] at hpk
    have hdvd' : p ∣ N.descFactorial k := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      exact Dvd.dvd.mul_left hdvd _
    rw [Nat.descFactorial_eq_prod_range] at hdvd'
    obtain ⟨i, hi, hpi'⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hdvd'
    rw [Finset.mem_range] at hi
    refine hcon (k - i - 1) (Finset.mem_range.2 (by omega)) p hp hpk ?_
    have : n + 1 + (k - i - 1) = N - i := by omega
    rw [this]
    exact hpi'
  rcases Nat.lt_or_ge k 26 with hk25 | hk25
  · rcases Nat.lt_or_ge n 200 with hn200 | hn200
    · obtain ⟨i, hi, p, hpmem, hkp, hpd⟩ :=
        small_cases k (Finset.mem_range.2 (by omega)) n (Finset.mem_range.2 hn200) hk h
      exact hcon i hi p (smallPrimes_prime p hpmem) hkp hpd
    · have h1 : N.choose k ≤ N ^ piCount k := choose_le_pow_piCount hNpos hH
      have h2 : N ^ k ≤ k ^ k * N.choose k := pow_le_pow_mul_choose (by omega)
      have h3 : k ^ k < 200 ^ (k - piCount k) :=
        small_pow_lt k (Finset.mem_range.2 (by omega)) hk
      have h4 : (200 : ℕ) ^ (k - piCount k) ≤ N ^ (k - piCount k) :=
        Nat.pow_le_pow_left (by omega) _
      have h5 : N ^ k < N ^ (k - piCount k) * N ^ piCount k := by
        calc N ^ k ≤ k ^ k * N.choose k := h2
          _ ≤ k ^ k * N ^ piCount k := by exact Nat.mul_le_mul_left _ h1
          _ < 200 ^ (k - piCount k) * N ^ piCount k := by
              exact mul_lt_mul_of_pos_right h3 (Nat.pow_pos hNpos)
          _ ≤ N ^ (k - piCount k) * N ^ piCount k := Nat.mul_le_mul_right _ h4
      rw [← pow_add] at h5
      rw [Nat.sub_add_cancel hpi] at h5
      exact absurd h5 (lt_irrefl _)
  · have hlow : 4 ^ k * N ^ k < k * ((2 * k) ^ k * N.choose k) :=
      four_pow_mul_pow_lt (by omega) (by omega)
    rcases Nat.lt_or_ge (N ^ 2) (k ^ 3) with hA | hA
    · rcases Nat.lt_or_ge k 20000 with hB | hB
      · have hn2 : n ^ 2 < k ^ 3 := by
          have : n ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
          omega
        have hk3 : k ^ 3 ≤ 19999 ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have hnlt : n < 2828300 := by
          by_contra hcc
          rw [not_lt] at hcc
          have hsq : (2828300 : ℕ) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hcc 2
          norm_num at hsq hk3
          omega
        obtain ⟨p, hp, h1, h2⟩ := exists_prime_in_Ioc (by omega) hnlt hn2
        exact hnoprime p hp h1 h2
      · have h1 : N.choose k ≤ N ^ Nat.sqrt N * 4 ^ min k (N / 3) :=
          choose_le_pow_sqrt_mul_four_pow (by omega) (by omega) hH
        have h2 := caseB hB (by omega) hA
        have hcontr : (4 : ℕ) ^ k * N ^ k < 4 ^ k * N ^ k := by
          calc 4 ^ k * N ^ k < k * ((2 * k) ^ k * N.choose k) := hlow
            _ ≤ k * ((2 * k) ^ k * (N ^ Nat.sqrt N * 4 ^ min k (N / 3))) := by
                exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
            _ ≤ 4 ^ k * N ^ k := h2
        exact absurd hcontr (lt_irrefl _)
    · have h1 : N.choose k ≤ N ^ piCount k := choose_le_pow_piCount hNpos hH
      have h2 : k ^ (k + 1) < 2 ^ k * N ^ (k - piCount k) :=
        caseA (by omega) hA (three_mul_piCount_le k)
      have hcontr : (4 : ℕ) ^ k * N ^ k < 4 ^ k * N ^ k := by
        calc 4 ^ k * N ^ k < k * ((2 * k) ^ k * N.choose k) := hlow
          _ ≤ k * ((2 * k) ^ k * N ^ piCount k) := by
              exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
          _ = 2 ^ k * k ^ (k + 1) * N ^ piCount k := by ring
          _ < 2 ^ k * (2 ^ k * N ^ (k - piCount k)) * N ^ piCount k := by
              have h6 : 2 ^ k * k ^ (k + 1) < 2 ^ k * (2 ^ k * N ^ (k - piCount k)) :=
                mul_lt_mul_of_pos_left h2 (Nat.pow_pos (by norm_num))
              exact mul_lt_mul_of_pos_right h6 (Nat.pow_pos hNpos)
          _ = 4 ^ k * (N ^ (k - piCount k) * N ^ piCount k) := by
              rw [show (4:ℕ) = 2 * 2 by norm_num, mul_pow]; ring
          _ = 4 ^ k * N ^ k := by
              rw [← pow_add, Nat.sub_add_cancel hpi]
      exact absurd hcontr (lt_irrefl _)

end Brockian.SylvesterSchur

