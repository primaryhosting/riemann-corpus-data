import Mathlib
namespace Brockian.OddPerfectMod4
/-- An odd perfect number is congruent to 1 modulo 4. Prove; axiom-clean, no sorry. -/
theorem oddPerfect_mod4 {n : ℕ} (ho : Odd n) (hp : Nat.Perfect n) : n % 4 = 1 := by
  -- An odd perfect number must be ≡ 1 (mod 4)
  -- Since n is odd, n % 4 ∈ {1, 3}
  have h_odd_mod : n % 4 = 1 ∨ n % 4 = 3 := by
    obtain ⟨k, hk⟩ := ho
    omega
  cases h_odd_mod with
  | inl h => exact h
  | inr h =>
    -- If n ≡ 3 (mod 4), derive contradiction from perfect number property
    -- The sum of proper divisors is n, so sum of all divisors is 2n
    have hsum : ∑ i ∈ n.divisors, i = 2 * n := by
      rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
      have := hp.1
      linarith
    -- All divisors of n are odd
    have hdiv_odd : ∀ d ∈ n.divisors, Odd d := by
      intro d hd
      exact ho.of_dvd_nat (Nat.dvd_of_mem_divisors hd)
    -- From hsum: σ(n) = 2n, so σ(n) % 4 = (2*n) % 4 = (2*3) % 4 = 2
    have hsigma_mod : (∑ i ∈ n.divisors, i) % 4 = 2 := by
      rw [hsum]
      omega
    -- Key: divisors come in pairs (d, n/d), and d + n/d ≡ 0 (mod 4) for each pair
    -- Since n ≡ 3 (mod 4), if d is odd then n/d is odd, and:
    -- - d ≡ 1 => n/d ≡ 3, so d + n/d ≡ 0 (mod 4)
    -- - d ≡ 3 => n/d ≡ 1, so d + n/d ≡ 0 (mod 4)
    -- So σ(n) ≡ 0 (mod 4), but σ(n) = 2n ≡ 2 (mod 4), contradiction!

    -- First show n is not a perfect square
    have hnsq : ¬IsSquare n := by
      rintro ⟨k, hk⟩
      have hk4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
      rcases hk4 with hk4 | hk4 | hk4 | hk4 <;> simp [hk, Nat.mul_mod, hk4] at h

    -- Get n ≠ 0
    have hne : n ≠ 0 := by
      intro hn0; have := hp.2; simp [hn0] at this

    -- For divisors pairing
    have hinv : ∀ d ∈ n.divisors, n / d ∈ n.divisors := by
      intro d hd
      have hdvd := Nat.dvd_of_mem_divisors hd
      rw [Nat.mem_divisors]
      exact ⟨Nat.div_dvd_of_dvd hdvd, hne⟩

    -- Let f(d) = n / d
    let f : ℕ → ℕ := fun d => n / d

    have hf_invol : ∀ d ∈ n.divisors, f (f d) = d := by
      intro d hd
      simp only [f]
      have hdvd := Nat.dvd_of_mem_divisors hd
      exact Nat.div_div_self hdvd hne

    have hpair : ∀ d ∈ n.divisors, d ≠ f d := by
      intro d hd hd_eq
      have hsq : n = d * d := by
        have hdiv := Nat.dvd_of_mem_divisors hd
        have h1 := Nat.div_mul_cancel hdiv
        have h2 : d = n / d := hd_eq
        nlinarith [h1, h2]
      exact hnsq ⟨d, hsq⟩

    -- Define S = {d ∈ divisors | d < f d}
    let S := (n.divisors).filter (fun d => d < f d)
    have hS : ∀ d, d ∈ S ↔ d ∈ n.divisors ∧ d < f d := fun d => by rw [Finset.mem_filter]

    -- S.card * 2 = n.divisors.card (pairing argument)
    have hcard : S.card * 2 = n.divisors.card := by
      have hfS : Finset.image f S = n.divisors \ S := by
        ext d
        simp only [Finset.mem_image, Finset.mem_sdiff]
        apply Iff.intro
        · rintro ⟨a, ha_S, rfl⟩
          rw [hS] at ha_S
          refine ⟨hinv a ha_S.1, ?_⟩
          rw [hS]
          intro ⟨_, ha_lt⟩
          simp only [hf_invol a ha_S.1] at ha_lt
          linarith [ha_S.2]
        · intro ⟨hd_dvd, hd_not_S⟩
          rw [hS] at hd_not_S
          push_neg at hd_not_S
          have hdf_d_lt : f d < d := by
            have hnot_lt : f d ≤ d := hd_not_S hd_dvd
            exact lt_of_le_of_ne hnot_lt (hpair d hd_dvd).symm
          have hdfdfd_lt : f d < f (f d) := by rw [hf_invol d hd_dvd]; exact hdf_d_lt
          exact ⟨f d, by rw [hS]; exact ⟨hinv d hd_dvd, hdfdfd_lt⟩, hf_invol d hd_dvd⟩
      have hsub : S ⊆ n.divisors := Finset.filter_subset _ _
      have hf_inj : Set.InjOn f n.divisors := by
        intro a ha b hb hab
        have ha' := hf_invol a ha
        have hb' := hf_invol b hb
        rw [hab] at ha'
        rw [hb'] at ha'
        exact ha'.symm
      have hcard_im : (Finset.image f S).card = S.card := by
        rw [Finset.card_image_iff]
        exact hf_inj.mono (by simp [hsub])
      have hfS : Finset.image f S = n.divisors \ S := by
        ext d
        simp only [Finset.mem_image, Finset.mem_sdiff]
        apply Iff.intro
        · rintro ⟨a, ha_S, rfl⟩
          rw [hS] at ha_S
          refine ⟨hinv a ha_S.1, ?_⟩
          rw [hS]
          intro ⟨_, ha_lt⟩
          simp only [hf_invol a ha_S.1] at ha_lt
          linarith [ha_S.2]
        · intro ⟨hd_dvd, hd_not_S⟩
          rw [hS] at hd_not_S
          push_neg at hd_not_S
          have hdf_d_lt : f d < d := by
            have hnot_lt : f d ≤ d := hd_not_S hd_dvd
            exact lt_of_le_of_ne hnot_lt (hpair d hd_dvd).symm
          have hdfdfd_lt : f d < f (f d) := by rw [hf_invol d hd_dvd]; exact hdf_d_lt
          exact ⟨f d, by rw [hS]; exact ⟨hinv d hd_dvd, hdfdfd_lt⟩, hf_invol d hd_dvd⟩
      rw [hfS] at hcard_im
      have hdisj : Disjoint S (n.divisors \ S) := Finset.disjoint_sdiff
      have hunion : S ∪ (n.divisors \ S) = n.divisors := Finset.union_sdiff_of_subset hsub
      rw [← hunion, Finset.card_union, hcard_im]
      simp [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
      omega

    -- Now compute the sum of divisors by grouping pairs
    -- For each d in S, we have d + f d in the sum
    -- d + f d ≡ 0 (mod 4) since one is 1 mod 4 and other is 3 mod 4

    -- First, let's show the pairing covers all divisors
    have hsum_pairs : ∑ i ∈ n.divisors, i = ∑ d ∈ S, (d + f d) := by
      -- n.divisors = S ∪ f(S) disjointly
      let fS := Finset.image f S
      have hfS : fS = n.divisors \ S := by
        apply Finset.ext
        intro d
        rw [Finset.mem_image, Finset.mem_sdiff]
        apply Iff.intro
        · rintro ⟨a, ha_S, ha_eq⟩
          rw [hS] at ha_S
          subst ha_eq
          refine ⟨hinv a ha_S.1, ?_⟩
          rw [hS]
          intro ⟨_, ha_lt⟩
          rw [hf_invol a ha_S.1] at ha_lt
          linarith [ha_S.2]
        · intro ⟨hd_dvd, hd_not_S⟩
          rw [hS] at hd_not_S
          push_neg at hd_not_S
          have hdf_d_lt : f d < d := by
            have hnot_lt : f d ≤ d := hd_not_S hd_dvd
            exact lt_of_le_of_ne hnot_lt (hpair d hd_dvd).symm
          have hdfdfd_lt : f d < f (f d) := by rw [hf_invol d hd_dvd]; exact hdf_d_lt
          exact ⟨f d, by rw [hS]; exact ⟨hinv d hd_dvd, hdfdfd_lt⟩, hf_invol d hd_dvd⟩
      have hsub : S ⊆ n.divisors := Finset.filter_subset _ _
      have hdisj : Disjoint S fS := by rw [hfS]; exact Finset.disjoint_sdiff
      have hunion : S ∪ fS = n.divisors := by rw [hfS]; exact Finset.union_sdiff_of_subset hsub
      -- Sum over union
      have hsum_union : ∑ i ∈ n.divisors, i = ∑ i ∈ S, i + ∑ i ∈ fS, i := by
        rw [← hunion]
        exact Finset.sum_union hdisj
      -- Sum over fS = sum over S of f
      have hf_inj : Set.InjOn f n.divisors := by
        intro a ha b hb hab
        have ha' := hf_invol a ha
        have hb' := hf_invol b hb
        rw [hab] at ha'
        rw [hb'] at ha'
        exact ha'.symm
      have hcard_im : fS.card = S.card := by
        rw [Finset.card_image_iff]
        exact hf_inj.mono hsub
      have hsum_fS : ∑ i ∈ fS, i = ∑ d ∈ S, f d := Finset.sum_image (hf_inj.mono hsub)
      rw [hsum_union, hsum_fS, ← Finset.sum_add_distrib]
    -- For each d in S, d is odd and f(d) = n/d is odd
    -- Since n ≡ 3 (mod 4): if d ≡ 1 then f(d) ≡ 3, if d ≡ 3 then f(d) ≡ 1
    -- So d + f(d) ≡ 0 (mod 4) for each pair
    have hsum_mod : (∑ d ∈ S, (d + f d)) % 4 = 0 := by
      -- Each term d + f(d) ≡ 0 (mod 4)
      have hterm : ∀ d ∈ S, (d + f d) % 4 = 0 := by
        intro d hd
        rw [hS] at hd
        have hd_odd := hdiv_odd d hd.1
        have hfd_odd := hdiv_odd (f d) (hinv d hd.1)
        have hdvd := Nat.dvd_of_mem_divisors hd.1
        have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
        -- d and n/d are both odd
        -- d % 4 ∈ {1, 3}, (n/d) % 4 ∈ {1, 3}
        -- d * (n/d) = n ≡ 3 (mod 4)
        have hd4 : d % 4 = 1 ∨ d % 4 = 3 := by
          obtain ⟨a, ha⟩ := hd_odd
          omega
        have hfd4 : (n / d) % 4 = 1 ∨ (n / d) % 4 = 3 := by
          have := hfd_odd
          simp only [f] at this
          obtain ⟨b, hb⟩ := this
          omega
        have hmul4 : (d * (n / d)) % 4 = 3 := by rw [hmul]; exact h
        -- Case analysis
        -- n / d * d = n, so (n / d) * d % 4 = 3
        have hmul4' : ((n / d) * d) % 4 = 3 := by rw [Nat.div_mul_cancel hdvd]; exact h
        -- d * (n/d) % 4 = (d % 4) * ((n/d) % 4) % 4
        have hmul_eq : d * (n / d) % 4 = (d % 4) * ((n / d) % 4) % 4 := Nat.mul_mod _ _ _
        rcases hd4 with hd4 | hd4 <;> rcases hfd4 with hfd4 | hfd4
        -- Case: d % 4 = 1, n/d % 4 = 1 => contradiction with hmul4
        · simp only [hd4, hfd4] at hmul_eq; omega
        -- Case: d % 4 = 1, n/d % 4 = 3 => d + n/d ≡ 0 (mod 4)
        · simp only [f]; omega
        -- Case: d % 4 = 3, n/d % 4 = 1 => d + n/d ≡ 0 (mod 4)
        · simp only [f]; omega
        -- Case: d % 4 = 3, n/d % 4 = 3 => contradiction with hmul4
        · simp only [hd4, hfd4] at hmul_eq; omega
      have hdiv : ∀ d ∈ S, 4 ∣ (d + f d) := fun d hd => Nat.dvd_of_mod_eq_zero (hterm d hd)
      exact Nat.mod_eq_zero_of_dvd (Finset.dvd_sum hdiv)
    -- But hsigma_mod says σ(n) % 4 = 2
    rw [hsum_pairs] at hsigma_mod
    omega
end Brockian.OddPerfectMod4
