import Mathlib
namespace Brockian.EvenSuperperfect

namespace EuclidEuler
namespace Nat

open ArithmeticFunction Finset
open scoped sigma

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_two_pow_eq_mersenne_succ]
  · simp [pr, sigma_one_apply]
  · positivity

theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by simp [ne_zero_of_prime_mersenne k pr, parity_simps]

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose! hm
    simp [hm]

end Nat
end EuclidEuler

open ArithmeticFunction in
theorem eq_two_pow_of_even_superperfect (n : ℕ) (hn : 0 < n) (he : Even n)
    (hσ : ArithmeticFunction.sigma 1 (ArithmeticFunction.sigma 1 n) = 2 * n) :
    ∃ k : ℕ, n = 2 ^ k := by
  -- Write n = 2^k * m with m odd
  obtain ⟨k, m, rfl, hm_odd⟩ := EuclidEuler.Nat.eq_two_pow_mul_odd hn
  have hm_odd' : Odd m := Nat.not_even_iff_odd.mp hm_odd
  -- Since gcd(2^k, m) = 1, σ is multiplicative
  have hcop : Nat.Coprime m (2 ^ k) := hm_odd'.coprime_two_right.pow_right _
  have hσ_mul : (sigma 1) (2 ^ k * m) = (sigma 1) (2 ^ k) * (sigma 1) m :=
    isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.symm hcop)
  have hσ_2k : (sigma 1) (2 ^ k) = 2 ^ (k + 1) - 1 := by
    rw [EuclidEuler.Nat.sigma_two_pow_eq_mersenne_succ, mersenne]
  -- Let S = σ(n) = (2^(k+1) - 1) * σ(m)
  set S := (sigma 1) (2 ^ k * m) with hS_def
  have hS : S = (2 ^ (k + 1) - 1) * (sigma 1) m := by rw [hσ_mul, hσ_2k]
  -- σ(S) = 2^(k+1) * m
  have hSS : (sigma 1) S = 2 ^ (k + 1) * m := by
    rw [hS_def] at hσ
    convert hσ using 1
    ring
  -- Key: show m = 1 by contradiction
  have hm_eq_1 : m = 1 := by
    by_contra hm_ne_1
    -- m ≥ 3 (m is odd and m ≠ 1)
    have hm_ge_3 : m ≥ 3 := by
      have hm_ne_0 : m ≠ 0 := by
        intro hm0
        rw [hm0, MulZeroClass.mul_zero] at hn
        norm_num at hn
      have hm_pos : m ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm_ne_0
      have hm_odd' : Odd m := hm_odd'
      obtain ⟨a, ha⟩ := hm_odd'
      omega
    -- σ(m) ≥ m + 1
    have hσm_ge_m1 : (sigma 1) m ≥ m + 1 := by
      rw [sigma_one_apply]
      have h1 : 1 ∈ Nat.divisors m := Nat.one_mem_divisors.mpr (by omega : m ≠ 0)
      have hm_div : m ∈ Nat.divisors m := Nat.mem_divisors_self m (by omega : m ≠ 0)
      -- Divisors include at least 1 and m, and they're distinct since m ≥ 3 > 1
      have h_distinct : (1 : ℕ) ≠ m := by omega
      have hsum : ∑ x ∈ ({1, m} : Finset ℕ), x = 1 + m := Finset.sum_pair h_distinct
      have hm_ne_0 : m ≠ 0 := by
        intro hm0
        rw [hm0, MulZeroClass.mul_zero] at hn
        norm_num at hn
      have hsub : ({1, m} : Finset ℕ) ⊆ Nat.divisors m := by
        simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_divisors, hm_ne_0]
      calc ∑ x ∈ Nat.divisors m, x ≥ ∑ x ∈ ({1, m} : Finset ℕ), x := Finset.sum_le_sum_of_subset hsub
        _ = 1 + m := hsum
        _ = m + 1 := by ring
    -- S ≥ (2^(k+1) - 1) * (m + 1)
    have hS_ge : S ≥ (2 ^ (k + 1) - 1) * (m + 1) := by
      rw [hS]
      exact Nat.mul_le_mul_left _ hσm_ge_m1
    -- σ(S) ≥ S + (2^(k+1) - 1) + σ(m) + 1 when S = (2^(k+1)-1) * σ(m) and both factors > 1
    -- Since σ(S) = 2^(k+1) * m
    -- We get: 2^(k+1) * m ≥ S + (2^(k+1) - 1) + σ(m) + 1
    --        = (2^(k+1) - 1) * σ(m) + (2^(k+1) - 1) + σ(m) + 1
    --        = 2^(k+1) * σ(m) + 2^(k+1)
    -- Key: σ(S) ≥ S + 1 (since 1 is a proper divisor)
    -- So 2^(k+1) * m ≥ S + 1 = (2^(k+1) - 1) * σ(m) + 1
    -- Combined with σ(m) ≥ m + 1:
    -- 2^(k+1) * m ≥ (2^(k+1) - 1) * (m + 1) + 1 = (2^(k+1) - 1) * m + 2^(k+1)
    -- So m ≥ 2^(k+1)
    -- But also: σ(S) ≥ S + (2^(k+1)-1) + σ(m) + 1 (when divisors distinct)
    -- This gives m ≥ σ(m) + 1 > m, contradiction.
    -- Let's first prove the weaker bound and see if it's enough
    have hS_pos : S ≥ 1 := by
      rw [hS]
      have h1 : 2 ^ (k + 1) - 1 ≥ 1 := Nat.sub_pos_of_lt (by simp)
      have h2 : (sigma 1) m ≥ 1 := by
        rw [sigma_one_apply]
        exact Finset.single_le_sum (fun x _ => Nat.zero_le x) (Nat.one_mem_divisors.mpr (by omega))
      exact Nat.mul_pos h1 h2
    have hSS_ge_S1 : (sigma 1) S ≥ S + 1 := by
      rw [sigma_one_apply]
      have hS_div : S ∈ Nat.divisors S := Nat.mem_divisors_self S (by omega : S ≠ 0)
      have h1_div : 1 ∈ Nat.divisors S := Nat.one_mem_divisors.mpr (by omega : S ≠ 0)
      -- S = (2^(k+1) - 1) * σ(m) ≥ 1 * (m + 1) ≥ 4 > 1
      have hS_gt_1 : S > 1 := by
        have h1 : 2 ^ (k + 1) - 1 ≥ 1 := Nat.sub_pos_of_lt (by simp)
        have h2 : (sigma 1) m ≥ m + 1 := hσm_ge_m1
        calc S = (2 ^ (k + 1) - 1) * (sigma 1) m := hS
          _ ≥ 1 * (m + 1) := Nat.mul_le_mul h1 h2
          _ = m + 1 := by simp
          _ ≥ 3 + 1 := by omega
          _ = 4 := by decide
          _ > 1 := by decide
      have hne : (1 : ℕ) ≠ S := by omega
      have hsum : (∑ x ∈ ({1, S} : Finset ℕ), x) = 1 + S := Finset.sum_pair hne
      calc ∑ x ∈ Nat.divisors S, x ≥ ∑ x ∈ ({1, S} : Finset ℕ), x := Finset.sum_le_sum_of_subset (by simp [Finset.insert_subset_iff, ne_of_gt (lt_of_lt_of_le zero_lt_one hS_pos)])
        _ = 1 + S := hsum
        _ = S + 1 := by ring
    -- From σ(S) = 2^(k+1) * m and σ(S) ≥ S + 1:
    -- 2^(k+1) * m ≥ S + 1 = (2^(k+1) - 1) * σ(m) + 1
    have hbound1 : 2 ^ (k + 1) * m ≥ (2 ^ (k + 1) - 1) * (sigma 1) m + 1 := by linarith
    -- From σ(m) ≥ m + 1:
    have hbound2 : 2 ^ (k + 1) * m ≥ (2 ^ (k + 1) - 1) * (m + 1) + 1 := by linarith
    -- (2^(k+1) - 1) * (m + 1) + 1 = (2^(k+1) - 1) * m + 2^(k+1)
    -- So 2^(k+1) * m ≥ (2^(k+1) - 1) * m + 2^(k+1)
    -- This simplifies to m ≥ 2^(k+1)
    set p := 2 ^ (k + 1) with hp_def
    have hp_pos : p ≥ 2 := by
      rw [hp_def]
      exact Nat.le_self_pow (by norm_num : k + 1 ≠ 0) 2
    -- hbound2: p * m ≥ (p - 1) * (m + 1) + 1
    -- Expanding: p * m ≥ p * m + p - m - 1 + 1 = p * m + p - m
    -- So 0 ≥ p - m, i.e., m ≥ p
    have hm_ge_p : m ≥ p := by
      have hle : p * m ≥ (p - 1) * (m + 1) + 1 := hbound2
      have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega : p ≥ 1)
      -- (p - 1) * (m + 1) = (p - 1) * m + (p - 1)
      have h_expand : (p - 1) * (m + 1) = (p - 1) * m + (p - 1) := Nat.mul_add_one (p - 1) m
      -- So (p - 1) * (m + 1) + 1 = (p - 1) * m + p
      have h_expand2 : (p - 1) * (m + 1) + 1 = (p - 1) * m + p := by omega
      -- So p * m ≥ (p - 1) * m + p
      rw [h_expand2] at hle
      -- p * m = (p - 1) * m + m
      have hp_eq : p * m = (p - 1) * m + m := by
        have := Nat.sub_add_cancel (by omega : p ≥ 1)
        calc p * m = ((p - 1) + 1) * m := by rw [this]
          _ = (p - 1) * m + m := by ring
      linarith
    -- We have m ≥ p = 2^(k+1) ≥ 2
    -- σ(m) ≥ m + 1 ≥ p + 1 > p - 1
    have hp_minus_1_lt_σm : p - 1 < (sigma 1) m := by
      have h1 : p - 1 < m + 1 := by omega
      linarith [hσm_ge_m1]
    -- Key observation: if k ≥ 1, then p ≥ 4, p - 1 ≥ 3
    -- S = (p-1) * σ(m) has distinct divisors 1, p-1, σ(m), S
    -- σ(S) ≥ 1 + (p-1) + σ(m) + S = p + σ(m) + S
    -- This gives m ≥ σ(m) + 1 > m, contradiction.
    -- For k = 0, p = 2, S = σ(m), σ(S) = 2m
    -- We need σ(σ(m)) = 2m with σ(m) ≥ m + 1 ≥ 4 (since m ≥ 3)
    -- σ(S) ≥ S + 1 gives 2m ≥ σ(m) + 1 ≥ m + 2, so m ≥ 2, which is fine.
    -- But for m odd ≥ 3, σ(m) is the sum of divisors of m.
    -- Since m ≥ p = 2^(k+1), and we also need a stronger constraint.
    -- Actually, let's just use: for any m > 1, σ(m) > m, so σ(σ(m)) ≥ σ(m) + 1.
    -- If S = σ(m), then σ(S) = 2m. So 2m ≥ σ(m) + 1 = S + 1.
    -- Combined with σ(m) ≥ m + 1: 2m ≥ m + 2, m ≥ 2. OK.
    -- We need: σ(m) < 2m for all m > 1 (m is not abundant in this specific way)
    -- Actually σ(m) can be > 2m for abundant numbers.
    -- Let's just check: if m = 2^j * q with q odd... but m is odd!
    -- For odd m, can σ(m) ≥ 2m? That would make m abundant.
    -- Smallest odd abundant number is 945. So for m < 945, σ(m) < 2m.
    -- But we don't have an upper bound on m.
    -- Different approach: use that m ≥ 2^(k+1). For k ≥ 1, m ≥ 4, so m ≥ 3 (since odd).
    -- The real issue: we derived m ≥ p from weak bound. For k = 0, p = 2, m ≥ 2.
    -- For k = 0: n = m (odd), σ(σ(n)) = 2n. So n is odd superperfect.
    -- Known: no odd superperfect numbers exist (open problem? or proven?)
    -- Actually this is an open problem! So we can't prove m = 1 for all cases.
    -- Wait, the theorem says n is EVEN. So n = 2^k * m with m odd and n even means k ≥ 1.
    -- That's the key! Since n is even, k ≥ 1, so p = 2^(k+1) ≥ 4.
    have hk_ge_1 : k ≥ 1 := by
      by_contra hk_lt_1
      push_neg at hk_lt_1
      interval_cases k
      simp [pow_zero] at hn he
      exact hm_odd he
    have hp_ge_4 : p ≥ 4 := by
      rw [hp_def]
      calc 2 ^ (k + 1) ≥ 2 ^ (1 + 1) := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)
        _ = 4 := by norm_num
    -- Now p - 1 ≥ 3 and σ(m) ≥ m + 1 ≥ p + 1 ≥ 5
    -- Divisors 1, p-1, σ(m), S are all distinct
    have hp1_ne_1 : p - 1 ≠ 1 := by omega
    have hσm_ne_1 : (sigma 1) m ≠ 1 := by omega
    have hp1_ne_σm : p - 1 ≠ (sigma 1) m := by omega
    have hσm_ge_2 : (sigma 1) m ≥ 2 := by linarith [hσm_ge_m1, hm_ge_p, hp_ge_4]
    have hp1_pos : p - 1 ≥ 1 := by omega
    have hS_eq : S = (p - 1) * (sigma 1) m := hS
    have hp1_ne_S : p - 1 ≠ S := by
      rw [hS_eq]
      intro heq
      have hσm_pos : (sigma 1) m > 0 := by omega
      -- If p - 1 = (p - 1) * σ(m), and σ(m) > 0, then σ(m) = 1
      have h : (p - 1) * (sigma 1) m = p - 1 := heq.symm
      have hle : p - 1 ≤ (p - 1) * (sigma 1) m := Nat.le_mul_of_pos_right _ hσm_pos
      have hge : (p - 1) * (sigma 1) m ≤ p - 1 := h.le
      -- So (sigma 1) m = 1
      have hp1_ne_zero : p - 1 ≠ 0 := by omega
      have hσm_eq_1 : (sigma 1) m = 1 := by
        have h2 : (p - 1) * (sigma 1) m = p - 1 := heq.symm
        have h3 : (p - 1) * (sigma 1) m = (p - 1) * 1 := by rw [h2, mul_one]
        exact Nat.mul_left_cancel hp1_pos h3
      omega
    have hσm_ne_S : (sigma 1) m ≠ S := by
      rw [hS_eq]
      intro heq
      have hp1_pos' : p - 1 > 0 := by omega
      -- If σ(m) = (p - 1) * σ(m), and p - 1 > 0, then p - 1 = 1
      have h : (p - 1) * (sigma 1) m = (sigma 1) m := heq.symm
      have hle : (sigma 1) m ≤ (p - 1) * (sigma 1) m := Nat.le_mul_of_pos_left _ hp1_pos'
      have hge : (p - 1) * (sigma 1) m ≤ (sigma 1) m := h.le
      have h_eq : (p - 1) * (sigma 1) m = (sigma 1) m := le_antisymm hge hle
      -- So p - 1 = 1
      have hσm_ne_zero : (sigma 1) m ≠ 0 := by omega
      have hp1_eq_1 : p - 1 = 1 := by
        have h2 : (p - 1) * (sigma 1) m = (sigma 1) m := heq.symm
        have h3 : (p - 1) * (sigma 1) m = 1 * (sigma 1) m := by rw [h2, one_mul]
        exact Nat.mul_right_cancel (by omega) h3
      omega
    -- Stronger bound: σ(S) ≥ 1 + S + (p-1) + σ(m)
    -- These are distinct divisors of S = (p-1) * σ(m)
    have hSS_strong_ge : (sigma 1) S ≥ 1 + S + (p - 1) + (sigma 1) m := by
      -- S has distinct divisors: 1, S, p-1, σ(m)
      -- Sum of these divisors: 1 + S + (p-1) + σ(m)
      -- First prove each is a divisor of S
      have h1_div : 1 ∈ Nat.divisors S := Nat.one_mem_divisors.mpr (by omega : S ≠ 0)
      have hS_div : S ∈ Nat.divisors S := Nat.mem_divisors_self S (by omega : S ≠ 0)
      have hp1_dvd : p - 1 ∣ S := by rw [hS_eq]; exact Nat.dvd_mul_right _ _
      have hs_dvd : (sigma 1) m ∣ S := by rw [hS_eq]; exact Nat.dvd_mul_left _ _
      have hp1_div : p - 1 ∈ Nat.divisors S := Nat.mem_divisors.mpr ⟨hp1_dvd, by omega⟩
      have hs_div : (sigma 1) m ∈ Nat.divisors S := Nat.mem_divisors.mpr ⟨hs_dvd, by omega⟩
      -- The set {1, S, p-1, σ(m)} is a subset of divisors of S
      have hsub : ({1, S, p - 1, (sigma 1) m} : Finset ℕ) ⊆ Nat.divisors S := by
        simp [Finset.insert_subset_iff, h1_div, hS_div, hp1_div, hs_div]
      -- Compute the sum over this subset
      have hS_ne_1 : S ≠ 1 := by
        have h1 : S ≥ (p - 1) * (m + 1) := hS_ge
        have h2 : p - 1 ≥ 1 := hp1_pos
        have h3 : m + 1 ≥ 4 := by omega
        have h4 : 1 * 4 ≤ (p - 1) * (m + 1) := Nat.mul_le_mul h2 h3
        have h5 : S ≥ 1 * 4 := h1.trans' h4
        omega
      have h1_ne_S : (1 : ℕ) ≠ S := ne_comm.mpr hS_ne_1
      have hS_ne_σm : S ≠ (sigma 1) m := ne_comm.mpr hσm_ne_S
      have h1_ne_σm : (1 : ℕ) ≠ (sigma 1) m := ne_comm.mpr hσm_ne_1
      have hS_ne_hp1 : S ≠ p - 1 := ne_comm.mpr hp1_ne_S
      have h1_ne_hp1 : (1 : ℕ) ≠ p - 1 := ne_comm.mpr hp1_ne_1
      have h1_ne_σm' : (1 : ℕ) ≠ (sigma 1) m := ne_comm.mpr hσm_ne_1
      have hsum : (∑ x ∈ ({1, S, p - 1, (sigma 1) m} : Finset ℕ), x) = 1 + S + (p - 1) + (sigma 1) m := by
        rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert]
        · simp [add_assoc]
        · simp [hp1_ne_σm]
        · simp [hS_ne_hp1, hS_ne_σm]
        · simp [h1_ne_S, h1_ne_hp1, h1_ne_σm']
      calc (sigma 1) S = ∑ x ∈ Nat.divisors S, x := by rw [sigma_one_apply]
        _ ≥ ∑ x ∈ ({1, S, p - 1, (sigma 1) m} : Finset ℕ), x := Finset.sum_le_sum_of_subset hsub
        _ = 1 + S + (p - 1) + (sigma 1) m := hsum
    -- Now derive contradiction:
    -- σ(S) = p * m ≥ (p - 1) + σ(m) + S + 1 = (p - 1) + σ(m) + (p-1)*σ(m) + 1
    --     = p + σ(m) + (p-1)*σ(m) = p + p*σ(m)
    -- So p*m ≥ p + p*σ(m), i.e., m ≥ 1 + σ(m) = σ(m) + 1
    -- But σ(m) ≥ m + 1, so m ≥ m + 2, contradiction!
    have hcontr : (sigma 1) S = p * m := by rw [hSS]
    have hf : p * m ≥ (p - 1) + (sigma 1) m + (p - 1) * (sigma 1) m + 1 := by
      have h1 : p * m = (sigma 1) S := hcontr.symm
      have h2 : (sigma 1) S ≥ 1 + S + (p - 1) + (sigma 1) m := hSS_strong_ge
      linarith [hS]
    -- Simplify: (p - 1) + s + (p - 1) * s + 1 = p + s + (p-1)*s = p + p*s
    set s := (sigma 1) m with hs_def
    have hf_simp : p * m ≥ p + p * s := by
      have hp_ge_1 : p ≥ 1 := by omega
      have h_expand : (p - 1) + s + (p - 1) * s + 1 = p + p * s := by
        have hp_ge_s : p ≥ 1 := hp_ge_1
        have hps_ge_s : p * s ≥ s := Nat.le_mul_of_pos_left s hp_ge_s
        rw [Nat.sub_mul, one_mul]
        omega
      linarith
    -- Divide by p: m ≥ 1 + σ(m)
    have hp_pos : p ≥ 1 := by omega
    -- p * m ≥ p + p * s means m ≥ 1 + s (dividing by p > 0)
    have hm_le : m ≥ 1 + s := by
      have := hf_simp
      have hp_pos' : p > 0 := by omega
      -- p * m ≥ p + p * s = p * (1 + s)
      have : p * m ≥ p * (1 + s) := by linarith [hf_simp]
      exact Nat.le_of_mul_le_mul_left this hp_pos'
    -- But σ(m) ≥ m + 1, so m ≥ m + 2, contradiction!
    omega
  exact ⟨k, by simp [hm_eq_1]⟩

open ArithmeticFunction in
/-- Even superperfect characterization: an even n satisfies σ(σ(n)) = 2n iff n = 2^(p−1)
    with 2^p − 1 a (Mersenne) prime. Uses ArithmeticFunction.sigma (Nat.sigma does not exist). -/
theorem even_superperfect_iff (n : ℕ) (hn : 0 < n) (he : Even n) :
    ArithmeticFunction.sigma 1 (ArithmeticFunction.sigma 1 n) = 2 * n ↔
      ∃ p : ℕ, (2 ^ p - 1).Prime ∧ n = 2 ^ (p - 1) := by
  constructor
  · -- Forward: σ(σ(n)) = 2n → n = 2^(p-1) with 2^p - 1 prime
    intro hσ
    obtain ⟨k, rfl⟩ := eq_two_pow_of_even_superperfect n hn he hσ
    use k + 1
    constructor
    · -- Show 2^(k+1) - 1 is prime
      -- We have σ(σ(2^k)) = 2 * 2^k = 2^(k+1)
      -- And σ(2^k) = 2^(k+1) - 1
      -- So σ(2^(k+1) - 1) = 2^(k+1) = (2^(k+1) - 1) + 1
      -- For m > 1, σ(m) = m + 1 iff m is prime
      have hσ2k : (sigma 1) (2 ^ k) = 2 ^ (k + 1) - 1 := by
        rw [EuclidEuler.Nat.sigma_two_pow_eq_mersenne_succ, mersenne]
      have hSS_eq : (sigma 1) (2 ^ (k + 1) - 1) = 2 ^ (k + 1) := by
        rw [← hσ2k]
        convert hσ using 1
        ring
      -- sum_properDivisors = σ(m) - m = 1, so m is prime
      have hk_pos : k ≥ 1 := by
        by_contra hk0
        push_neg at hk0
        interval_cases k
        simp [even_iff_two_dvd] at he
      have hm_gt_1 : 2 ^ (k + 1) - 1 > 1 := by
        have h1 : 2 ^ (k + 1) > 2 := by
          have : 1 < k + 1 := Nat.lt_succ_of_le hk_pos
          exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) this
        omega
      have hsum_prop : ∑ i ∈ Nat.properDivisors (2 ^ (k + 1) - 1), i = 1 := by
        simp only [sigma_one_apply] at hSS_eq
        rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hSS_eq
        omega
      exact Nat.sum_properDivisors_eq_one_iff_prime.mp hsum_prop
    · simp
  · -- Backward: n = 2^(p-1) with 2^p - 1 prime → σ(σ(n)) = 2n
    rintro ⟨p, hp_prime, rfl⟩
    -- n = 2^(p-1), need to show σ(σ(n)) = 2n
    -- σ(n) = σ(2^(p-1)) = mersenne(p) = 2^p - 1
    -- Since 2^p - 1 is prime, σ(2^p - 1) = 1 + (2^p - 1) = 2^p = 2 * 2^(p-1) = 2n
    have hp_pos : 0 < p := by
      by_contra hp0
      push_neg at hp0
      interval_cases p
      exact Nat.not_prime_zero hp_prime
    have hσ1 : (sigma 1) (2 ^ (p - 1)) = 2 ^ p - 1 := by
      rw [EuclidEuler.Nat.sigma_two_pow_eq_mersenne_succ, mersenne, Nat.sub_add_cancel hp_pos]
    rcases p with ⟨⟩
    · contradiction
    · -- p = n + 1
      rename_i n
      rw [hσ1]
      -- Now need σ(2^(n+1) - 1) = 2 * 2^n
      -- Since 2^(n+1) - 1 is prime, σ(2^(n+1) - 1) = 1 + (2^(n+1) - 1) = 2^(n+1)
      have hprime : Nat.Prime (2 ^ (n + 1) - 1) := hp_prime
      rw [sigma_one_apply]
      -- For prime p, divisors are {1, p}, sum is 1 + p
      rw [Nat.Prime.sum_divisors hprime]
      simp [pow_succ]
      rw [Nat.sub_add_cancel (by linarith [pow_pos (by norm_num : 0 < (2:ℕ)) n] : 1 ≤ 2 ^ n * 2)]
      ring
end Brockian.EvenSuperperfect

