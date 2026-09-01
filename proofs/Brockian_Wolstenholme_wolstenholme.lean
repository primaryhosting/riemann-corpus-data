import Mathlib
namespace Brockian.Wolstenholme
/-- Wolstenholme's theorem: for a prime p ≥ 5, p^3 divides C(2p, p) − 2. -/
theorem wolstenholme (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 3 ∣ (Nat.choose (2 * p) p : ℤ) - 2 := by
  let q (p i : ℕ) : ℕ := p.choose i / p
  have choose_eq_mul_q (p i : ℕ) (hp : p.Prime) (hi0 : i ≠ 0) (hip : i < p) :
      p.choose i = p * q p i := by
    have h : p ∣ p.choose i := by
      apply Nat.Prime.dvd_choose_self hp hi0
      exact hip
    rw [← Nat.mul_div_cancel' h]

  have q_mul_cast (p i : ℕ) (hp : p.Prime) (hi0 : i ≠ 0) (hip : i < p) :
      (q p i : ZMod p) * i = (-1 : ZMod p) ^ (i - 1) := by
    have h1 : i * Nat.choose p i = p * Nat.choose (p - 1) (i - 1) := by
      cases i with
      | zero => contradiction
      | succ j =>
        cases p with
        | zero => contradiction
        | succ k =>
          simp +arith [Nat.add_one_mul_choose_eq, Nat.choose_succ_succ]
          ring
    -- From h1: i * p.choose i = p * (p-1).choose (i-1)
    -- And p.choose i = p * q p i
    -- So i * p * q p i = p * (p-1).choose (i-1)
    -- Hence q p i * i = (p-1).choose (i-1)
    have h2 : q p i * i = Nat.choose (p - 1) (i - 1) := by
      have hpc := choose_eq_mul_q p i hp hi0 hip
      have hppos : 0 < p := hp.pos
      have key : i * p.choose i = p * (q p i * i) := by rw [hpc]; ring
      rw [h1] at key
      exact Nat.mul_right_inj hppos.ne' |>.mp key.symm
    -- Now we need: (p-1).choose (i-1) ≡ (-1)^(i-1) (mod p)
    rw [← Nat.cast_mul, h2]
    have hik : i - 1 < p := by omega
    haveI : NeZero p := ⟨hp.ne_zero⟩
    -- We need to show (p-1).choose (i-1) ≡ (-1)^(i-1) (mod p)
    -- Use induction on (i-1)
    have hik' : i - 1 ≤ p - 1 := by omega
    -- Prove a helper lemma by induction
    have h_lemma : ∀ k ≤ p - 1, ((p - 1).choose k : ZMod p) = (-1) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro hk
        have hk' : k ≤ p - 1 := by omega
        -- Key identity: (k+1) * C(p-1, k+1) = C(p-1, k) * (p-1-k)
        have h_id : (k + 1) * Nat.choose (p - 1) (k + 1) = Nat.choose (p - 1) k * (p - 1 - k) := by
          have := Nat.choose_succ_right_eq (p - 1) k
          linarith
        -- In ZMod p: (k+1) * C(p-1, k+1) = C(p-1, k) * (p-1-k) = C(p-1, k) * (-(k+1))
        have h_pmk_zmod : ((p - 1 - k : ℕ) : ZMod p) = (-(k + 1) : ZMod p) := by
          have h_eq : (p - 1 - k : ℕ) = p - (k + 1) := by omega
          rw [h_eq]
          have hpk : k + 1 ≤ p := by omega
          norm_cast
          rw [Nat.cast_sub hpk]
          simp
        -- ih gives us: (p-1).choose k = (-1)^k in ZMod p
        have ihk := ih hk'
        -- From h_id cast to ZMod p: (k+1) * C(p-1, k+1) = C(p-1, k) * (p-1-k)
        have h_id_zmod : ((k + 1 : ℕ) : ZMod p) * ((p - 1).choose (k + 1) : ZMod p) =
                         ((p - 1).choose k : ZMod p) * ((p - 1 - k : ℕ) : ZMod p) := by
          have := congr_arg (· : ℕ → ZMod p) h_id
          simp only [Nat.cast_mul] at this ⊢
          exact this
        rw [ihk, h_pmk_zmod] at h_id_zmod
        -- Now: (k+1) * C(p-1, k+1) = (-1)^k * (-(k+1)) = (-1)^(k+1) * (k+1)
        have h_bound : k + 1 < p := by omega
        have h_cancel : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
          intro h
          rw [ZMod.natCast_eq_zero_iff] at h
          exact Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < k + 1) h_bound h
        have h_eq : ((k + 1 : ℕ) : ZMod p) * ((p - 1).choose (k + 1) : ZMod p) =
                    ((k + 1 : ℕ) : ZMod p) * ((-1 : ZMod p) ^ (k + 1)) := by
          rw [h_id_zmod]
          rw [pow_succ]
          have : ((k + 1 : ℕ) : ZMod p) = ((k : ℕ) : ZMod p) + 1 := by norm_cast
          rw [this]
          ring
        haveI := Fact.mk hp
        exact mul_left_cancel₀ h_cancel h_eq
    exact h_lemma (i - 1) hik'

  have sum_q_sq_dvd (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
      p ∣ ∑ i ∈ Finset.Ico 1 p, (q p i) ^ 2 := by
    haveI : Fact p.Prime := ⟨hp⟩
    -- Show that p ∣ sum by working in ZMod p
    suffices h : ((∑ i ∈ Finset.Ico 1 p, (q p i) ^ 2 : ℕ) : ZMod p) = 0 by
      apply Nat.dvd_of_mod_eq_zero
      have := ZMod.val_natCast (n := p) (∑ i ∈ Finset.Ico 1 p, (q p i) ^ 2)
      simp_all
    -- Rewrite sum in ZMod p
    simp only [Nat.cast_sum]
    -- For each i in [1, p), (q p i : ZMod p) ^ 2 = (i⁻¹ : ZMod p) ^ 2
    have key : ∀ i ∈ Finset.Ico 1 p, ((q p i : ℕ) : ZMod p) ^ 2 = ((i : ZMod p)⁻¹) ^ 2 := by
      intro i hi
      have ⟨hi1, hip⟩ := Finset.mem_Ico.mp hi
      have hi0 : i ≠ 0 := Nat.one_le_iff_ne_zero.mp hi1
      have hiunit : (i : ZMod p) ≠ 0 := by
        simp only [ne_eq, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi0) hip
      have hiinv := q_mul_cast p i hp hi0 hip
      have hi_inv_eq : (q p i : ZMod p) = (-1 : ZMod p) ^ (i - 1) * (i : ZMod p)⁻¹ := by
        calc (q p i : ZMod p) = (q p i : ZMod p) * (i : ZMod p) * (i : ZMod p)⁻¹ := by
               field_simp
          _ = (-1 : ZMod p) ^ (i - 1) * (i : ZMod p)⁻¹ := by rw [hiinv]
      rw [hi_inv_eq]
      have : ((-1 : ZMod p) ^ (i - 1) * (i : ZMod p)⁻¹) ^ 2 = ((-1 : ZMod p) ^ (i - 1)) ^ 2 * ((i : ZMod p)⁻¹) ^ 2 := by ring
      rw [this]
      have h1 : ((-1 : ZMod p) ^ (i - 1)) ^ 2 = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        simp
      simp_all
    -- First convert Nat.cast of square to square of Nat.cast
    simp only [Nat.cast_pow]
    -- Rewrite the sum using key
    rw [Finset.sum_congr rfl key]
    -- Use bijection i ↦ i⁻¹
    -- We'll show that ∑ (i⁻¹)² = ∑ j² by noting that inversion is a bijection
    -- And ∑_{j=1}^{p-1} j² = (p-1)p(2p-1)/6 ≡ 0 [ZMOD p]
    have sum_inv_sq_eq_sum_sq : ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p)⁻¹) ^ 2 = ∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)) ^ 2 := by
      -- Key insight: The sum ∑ i ∈ {1,...,p-1}, (i⁻¹)² = ∑ j ∈ {1,...,p-1}, j²
      -- because the map i ↦ i⁻¹ is a bijection on the nonzero elements of ZMod p
      -- We'll use Finset.sum_bij' with the inverse function
      -- We use the fact that the sum over nonzero elements equals sum over their inverses
      -- First establish that Finset.Ico 1 p maps bijectively to Finset.univ.erase 0 in ZMod p
      have h_image : Finset.image (fun i : ℕ => (i : ZMod p)) (Finset.Ico 1 p) = Finset.univ.erase 0 := by
        ext x
        simp [Finset.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨a, ⟨ha1, hap⟩, rfl⟩
          simp only [ZMod.natCast_eq_zero_iff]
          exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp ha1)) hap
        · intro hx
          use x.val
          refine ⟨⟨Nat.pos_of_ne_zero ?_, x.val_lt⟩, ?_⟩
          · simp [hx]
          · simp [ZMod.natCast_val]
      -- Use h_image to rewrite the sums
      -- The sum over Finset.Ico 1 p equals the sum over Finset.univ.erase 0 in ZMod p
      have h_inj : Set.InjOn (fun i : ℕ => (i : ZMod p)) (Finset.Ico 1 p) := by
        intro a ha b hb hab
        simp only [ZMod.natCast_eq_natCast_iff] at hab
        exact hab.eq_of_lt_of_lt (Finset.mem_Ico.mp ha).2 (Finset.mem_Ico.mp hb).2
      have h_sum_eq : (∑ i ∈ Finset.Ico 1 p, ((i : ZMod p)⁻¹) ^ 2 : ZMod p) = ∑ x ∈ Finset.univ.erase 0, (x⁻¹) ^ 2 := by
        conv_rhs => rw [← h_image]
        rw [Finset.sum_image h_inj]
      have h_sum_eq2 : (∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)) ^ 2 : ZMod p) = ∑ x ∈ Finset.univ.erase 0, (x) ^ 2 := by
        conv_rhs => rw [← h_image]
        rw [Finset.sum_image h_inj]
      rw [h_sum_eq, h_sum_eq2]
      -- Now show that ∑ x ∈ F*, (x⁻¹)² = ∑ x ∈ F*, x²
      -- This is true because x ↦ x⁻¹ is a bijection on F*
      -- We use the fact that the map x ↦ x⁻¹ is a bijection on (ZMod p)ˣ
      -- Use a direct bijection: the inverse map is an involution on nonzero elements
      have key2 : ∀ x ∈ Finset.univ.erase (0 : ZMod p), (x⁻¹)⁻¹ = x := by
        intro x hx
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
        rw [inv_inv]
      have hmaps : ∀ x ∈ Finset.univ.erase (0 : ZMod p), x⁻¹ ∈ Finset.univ.erase (0 : ZMod p) := by
        intro x hx
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx ⊢
        simp [hx]
      have h_equiv : (Finset.univ.erase (0 : ZMod p)).sum (fun x => x⁻¹ ^ 2) =
                     (Finset.univ.erase 0).sum (fun x => (Equiv.inv (G := ZMod p) x) ^ 2) := rfl
      have h_eq : ∀ x ∈ Finset.univ.erase (0 : ZMod p), x⁻¹ ^ 2 = (Equiv.inv (ZMod p) x) ^ 2 := by
        intro x hx
        rw [Equiv.inv_apply]
      rw [Finset.sum_congr rfl h_eq]
      refine Finset.sum_nbij (fun x => Equiv.inv (ZMod p) x) ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha ⊢
        simp [ha]
      · intro a ha b hb hab
        simp only at hab
        have : Equiv.inv (ZMod p) (Equiv.inv (ZMod p) a) = Equiv.inv (ZMod p) (Equiv.inv (ZMod p) b) := by rw [hab]
        simp [inv_inv] at this
        exact this
      · intro b hb
        have hb' : b ≠ 0 := Finset.mem_erase.mp hb |>.1
        use Equiv.inv (ZMod p) b
        simp [hb']
      · intro a ha
        rfl
    -- Now show that ∑_{j=1}^{p-1} j² = 0 in ZMod p
    have sum_sq_zero : ∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)) ^ 2 = 0 := by
      -- Convert to sum_range
      rw [Finset.sum_Ico_eq_sum_range]
      -- ∑_{k=0}^{p-2} (k+1)² = (p-1)p(2p-1)/6
      simp only [add_comm]
      -- The sum equals (p-1)p(2p-1)/6, and p = 0 in ZMod p
      -- Now we need ∑ k ∈ range (p-1), (k+1)² = 0
      -- This equals (p-1)p(2p-1)/6 which is 0 in ZMod p since p | numerator
      -- Use the sum of squares formula: ∑_{k=0}^{n-1} (k+1)² = n(n+1)(2n+1)/6
      have sum_sq_formula : ∀ n : ℕ, ∑ k ∈ Finset.range n, ((k + 1) : ZMod p) ^ 2 = 
                           ((n : ZMod p) * ((n : ZMod p) + 1) * (2 * (n : ZMod p) + 1) : ZMod p) * 6⁻¹ := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          -- Need to show: n*(n+1)*(2n+1)*6⁻¹ + (n+1)² = (n+1)*(n+2)*(2n+3)*6⁻¹
          have h6 : (6 : ZMod p) ≠ 0 := by
            intro h6eq
            have h6eq' : ((6 : ℕ) : ZMod p) = 0 := h6eq
            rw [ZMod.natCast_eq_zero_iff] at h6eq'
            have : p ∣ 6 := h6eq'
            have hpb : p ≤ 6 := Nat.le_of_dvd (by norm_num) this
            interval_cases p
            · contradiction  -- p = 5, but 5 ∤ 6
            · contradiction  -- p = 6, but 6 is not prime
          field_simp
          norm_cast
          ring_nf
      -- Apply the formula with n = p - 1
      apply Eq.trans (Finset.sum_congr rfl fun x _ => ?_)
      · rw [sum_sq_formula (p - 1)]
        -- (p-1) + 1 = p = 0 in ZMod p
        have hp1 : ((p - 1 : ℕ) : ZMod p) + 1 = 0 := by
          have h : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
          norm_cast
          simp [h]
        rw [hp1]
        ring
      · simp [Nat.cast_add]
    rw [sum_inv_sq_eq_sum_sq, sum_sq_zero]

  have central_choose_sub_two (p : ℕ) (hp : 0 < p) :
      (Nat.choose (2 * p) p : ℤ) - 2 =
        ∑ i ∈ Finset.Ico 1 p, (Nat.choose p i : ℤ) ^ 2 := by
    rw [Finset.sum_Ico_eq_sub _ hp]
    -- Need to show: (2p choose p) - 2 = ∑_{k=0}^{p-1} (p choose k)^2 - 1
    -- Identity: (2p choose p) = ∑_{k=0}^{p} (p choose k)^2
    have vid : (2 * p).choose p = ∑ k ∈ Finset.range (p + 1), (p.choose k) ^ 2 := by
      exact (Nat.sum_range_choose_sq p).symm
    simp [Finset.sum_range_succ, vid]
    omega
  -- Use central_choose_sub_two to rewrite in terms of sum of squares
  have h1 : (Nat.choose (2 * p) p : ℤ) - 2 = ∑ i ∈ Finset.Ico 1 p, (Nat.choose p i : ℤ) ^ 2 := 
    central_choose_sub_two p hp.pos
  rw [h1]
  -- Each C(p,i) = p * q(p,i), so C(p,i)^2 = p^2 * q(p,i)^2
  have h2 : ∑ i ∈ Finset.Ico 1 p, (Nat.choose p i : ℤ) ^ 2 = 
            p ^ 2 * ∑ i ∈ Finset.Ico 1 p, (q p i : ℤ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have ⟨hi1, hip⟩ := Finset.mem_Ico.mp hi
    have hi0 : i ≠ 0 := Nat.one_le_iff_ne_zero.mp hi1
    rw [choose_eq_mul_q p i hp hi0 hip]
    simp [Nat.cast_mul]
    ring
  rw [h2]
  -- Since p divides ∑ q(p,i)^2, we have p^3 = p^2 * p divides p^2 * ∑q(p,i)^2
  have h3 : (p : ℤ) ∣ ∑ i ∈ Finset.Ico 1 p, (q p i : ℤ) ^ 2 := by
    have := sum_q_sq_dvd p hp h5
    norm_cast
  exact mul_dvd_mul_left (p ^ 2 : ℤ) h3
end Brockian.Wolstenholme

