import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/
def Kset (n : ℕ) (δ : ℝ) : Set (Fin n → ℝ) := {x | (∀ i, δ ≤ x i) ∧ ∑ i, x i = 1}

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}

lemma Kset_nonneg {δ : ℝ} (hδ : 0 ≤ δ) {x : Fin n → ℝ} (hx : x ∈ Kset n δ) (i : Fin n) :
    0 ≤ x i := le_trans hδ (hx.1 i)

lemma Kset_le_one {δ : ℝ} (hδ : 0 ≤ δ) {x : Fin n → ℝ} (hx : x ∈ Kset n δ) (i : Fin n) :
    x i ≤ 1 := by
  have hnonneg : ∀ j, 0 ≤ x j := fun j => le_trans hδ (hx.1 j)
  calc x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    _ = 1 := hx.2

lemma Kset_ne_zero {δ : ℝ} {x : Fin n → ℝ} (hx : x ∈ Kset n δ) :
    x ≠ 0 := by
  rintro rfl
  simp [Kset] at hx

lemma isCompact_Kset (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : IsCompact (Kset n δ) := by
  -- Kset is a closed subset of the compact set [δ, 1]^n
  have hsub : Kset n δ ⊆ Set.Icc (fun _ : Fin n => δ) (fun _ => 1) := by
    intro x hx
    exact ⟨fun i => hx.1 i, fun i => Kset_le_one hδ hx i⟩
  have hclosed : IsClosed (Kset n δ) := by
    simp only [Kset]
    have h1 : IsClosed {x : Fin n → ℝ | ∀ i, δ ≤ x i} := by
      have : {x : Fin n → ℝ | ∀ i, δ ≤ x i} = ⋂ i : Fin n, {x | δ ≤ x i} := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le (continuous_const : Continuous (fun _ : Fin n → ℝ => δ)) (@continuous_apply (Fin n) (fun _ : Fin n => ℝ) _ i)
    have h2 : IsClosed {x : Fin n → ℝ | ∑ i, x i = 1} := by
      exact isClosed_eq (continuous_finset_sum _ fun i _ => @continuous_apply (Fin n) (fun _ : Fin n => ℝ) _ i) continuous_const
    exact h1.inter h2
  exact IsCompact.of_isClosed_subset (isCompact_Icc (α := Fin n → ℝ)) hclosed hsub

/-- The Collatz–Wielandt set: pairs `(t, x)` with `x` in `Kset n δ` and `t • x ≤ M x`. -/
def Cset (M : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  {p | 0 ≤ p.1 ∧ p.2 ∈ Kset n δ ∧ ∀ i, p.1 * p.2 i ≤ M.mulVec p.2 i}

lemma isCompact_Cset (M : Matrix (Fin n) (Fin n) ℝ) {δ B : ℝ} (hδ : 0 < δ)
    (hB : ∀ i j, M i j ≤ B) : IsCompact (Cset M δ) := by
  by_cases hB_nonneg : B ≥ 0
  · -- Case B ≥ 0: Cset M δ is a closed subset of [0, B/δ] × Kset n δ
    have hBdiv : B / δ ≥ 0 := div_nonneg hB_nonneg (le_of_lt hδ)
    -- Cset is closed
    have hclosed : IsClosed (Cset M δ) := by
      simp only [Cset]
      apply IsClosed.inter
      · exact isClosed_le continuous_const continuous_fst
      · apply IsClosed.inter
        · exact isCompact_Kset n (le_of_lt hδ) |>.isClosed.preimage continuous_snd
        · change IsClosed {p : ℝ × (Fin n → ℝ) | ∀ i, p.1 * p.2 i ≤ M.mulVec p.2 i}
          rw [show {p : ℝ × (Fin n → ℝ) | ∀ i, p.1 * p.2 i ≤ M.mulVec p.2 i} = ⋂ i, {p | p.1 * p.2 i ≤ M.mulVec p.2 i} by ext; simp]
          apply isClosed_iInter
          intro i
          have h1 : Continuous (fun p : ℝ × (Fin n → ℝ) => p.1 * p.2 i) := continuous_fst.mul ((continuous_apply i).comp continuous_snd)
          have h2 : Continuous (fun p : ℝ × (Fin n → ℝ) => M.mulVec p.2 i) := by
            simp only [Matrix.mulVec, dotProduct]
            exact continuous_finset_sum _ (fun j _ => continuous_const.mul ((continuous_apply j).comp continuous_snd))
          exact isClosed_le h1 h2
    -- Cset M δ ⊆ [0, B/δ] × Kset n δ
    have hsubset : Cset M δ ⊆ Set.Icc 0 (B / δ) ×ˢ Kset n δ := by
      intro p hp
      obtain ⟨ht, hxKset, hineq⟩ := hp
      simp only [Set.mem_prod, Set.mem_Icc]
      refine ⟨⟨ht, ?_⟩, hxKset⟩
      have hn : 0 < n := by
        by_contra hn0
        have hn0' : n = 0 := Nat.eq_zero_of_not_pos hn0
        have : Kset n δ = ∅ := by
          subst hn0'
          ext x
          simp [Kset]
        rw [this] at hxKset
        exact hxKset
      have hxδ : p.2 ⟨0, hn⟩ ≥ δ := hxKset.1 ⟨0, hn⟩
      have hineq0 := hineq ⟨0, hn⟩
      have hmulvec : M.mulVec p.2 ⟨0, hn⟩ ≤ B := by
        calc M.mulVec p.2 ⟨0, hn⟩ = ∑ j, M ⟨0, hn⟩ j * p.2 j := rfl
          _ ≤ ∑ j, B * p.2 j := by apply Finset.sum_le_sum; intro j _; nlinarith [hB ⟨0, hn⟩ j, hxKset.1 j]
          _ = B * ∑ j, p.2 j := by rw [mul_sum]
          _ = B * 1 := by rw [hxKset.2]
          _ = B := mul_one B
      rw [le_div_iff₀ hδ]
      have hkey : p.1 * p.2 ⟨0, hn⟩ ≤ B := le_trans hineq0 hmulvec
      have hmul : p.1 * δ ≤ p.1 * p.2 ⟨0, hn⟩ := by nlinarith
      linarith
    -- [0, B/δ] × Kset n δ is compact
    have hcompact : IsCompact (Set.Icc 0 (B / δ) ×ˢ Kset n δ) :=
      isCompact_Icc.prod (isCompact_Kset n (le_of_lt hδ))
    -- Cset M δ is a closed subset, hence compact
    exact hcompact.of_isClosed_subset hclosed hsubset
  · -- Case B < 0: Cset M δ is empty
    have hempty : Cset M δ = ∅ := by
      by_cases hn : n = 0
      · subst hn
        ext ⟨t, x⟩
        simp [Cset, show (Kset 0 δ) = ∅ from by ext x; simp [Kset]]
      · ext ⟨t, x⟩
        simp only [Set.mem_empty_iff_false, iff_false]
        rw [Cset]
        simp only [Set.mem_setOf_eq]
        rintro ⟨ht, hxKset, hle⟩
        have hn' : 0 < n := Nat.pos_of_ne_zero hn
        have hxδ := hxKset.1 ⟨0, hn'⟩
        have hineq0 := hle ⟨0, hn'⟩
        have hmulvec : M.mulVec x ⟨0, hn'⟩ ≤ B := by
          calc M.mulVec x ⟨0, hn'⟩ = ∑ j, M ⟨0, hn'⟩ j * x j := rfl
            _ ≤ ∑ j, B * x j := by apply Finset.sum_le_sum; intro j _; nlinarith [hB ⟨0, hn'⟩ j, hxKset.1 j]
            _ = B * ∑ j, x j := by rw [mul_sum]
            _ = B * 1 := by rw [hxKset.2]
            _ = B := mul_one B
        nlinarith
    exact hempty ▸ isCompact_empty

lemma mulVec_pos (hpos : ∀ i j, 0 < M i j) {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hx0 : x ≠ 0) (i : Fin n) : 0 < M.mulVec x i := by
  -- Since x ≠ 0 and all x i ≥ 0, there exists some k with x k > 0
  obtain ⟨k, hk⟩ : ∃ k, 0 < x k := by
    by_contra h
    push_neg at h
    exact hx0 (funext fun j => le_antisymm (h j) (hx j))
  -- Since M i k > 0 and x k > 0, we have M i k * x k > 0
  have hterm : 0 < M i k * x k := mul_pos (hpos i k) hk
  -- M.mulVec x i ≥ M i k * x k since it's a sum of nonneg terms
  have hge : M i k * x k ≤ M.mulVec x i := by
    simp [Matrix.mulVec]
    apply Finset.single_le_sum (fun j _ => mul_nonneg (le_of_lt (hpos i j)) (hx j))
    simp
  linarith

/-- Existence of a uniform lower bound `δ` for normalized images, and an entry bound `B`. -/
lemma exists_delta (hn : 0 < n) (hpos : ∀ i j, 0 < M i j) :
    ∃ δ B : ℝ, 0 < δ ∧ δ ≤ (n : ℝ)⁻¹ ∧ (∀ i j, M i j ≤ B) ∧
      ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
        (fun i => M.mulVec x i / ∑ j, M.mulVec x j) ∈ Kset n δ := by
  -- Let's pick δ small enough and B large enough
  let minM := sInf (Set.range (fun p : Fin n × Fin n => M p.1 p.2))
  let maxM := sSup (Set.range (fun p : Fin n × Fin n => M p.1 p.2))
  -- The set of matrix entries is finite and nonempty
  have hne : Set.Nonempty (Set.range (fun p : Fin n × Fin n => M p.1 p.2)) :=
    ⟨M ⟨0, hn⟩ ⟨0, hn⟩, ⟨(⟨0, hn⟩, ⟨0, hn⟩), rfl⟩⟩
  have hfin : Set.Finite (Set.range (fun p : Fin n × Fin n => M p.1 p.2)) := Set.finite_range _
  -- minM > 0 since all entries are positive
  have hminM_pos : 0 < minM := by
    have hbound : ∀ y ∈ Set.range (fun p : Fin n × Fin n => M p.1 p.2), 0 < y := by
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact hpos i j
    -- Use a Finset and inf'
    let s := Finset.image (fun p : Fin n × Fin n => M p.1 p.2) Finset.univ
    have hs_eq : (s : Set ℝ) = Set.range (fun p : Fin n × Fin n => M p.1 p.2) := by
      ext y; simp [s]
    have hs_nonempty : s.Nonempty := ⟨M ⟨0, hn⟩ ⟨0, hn⟩, by simp [s]⟩
    have h_eq : minM = s.min' hs_nonempty := by
      simp only [minM]
      apply le_antisymm
      · apply csInf_le hfin.bddBelow
        exact hs_eq ▸ Finset.min'_mem _ _
      · exact le_csInf hne (fun y hy => by
          have hy' : y ∈ s := hs_eq.symm.subset hy
          exact Finset.min'_le _ _ hy')
    rw [h_eq]
    have hmin'_mem : s.min' hs_nonempty ∈ s := Finset.min'_mem _ _
    rw [Finset.mem_image] at hmin'_mem
    obtain ⟨⟨i, j⟩, _, h_eq2⟩ := hmin'_mem
    rw [← h_eq2]
    exact hbound _ ⟨⟨i, j⟩, rfl⟩
  -- maxM bounds all entries
  have hmaxM_ub : ∀ i j, M i j ≤ maxM := by
    intro i j
    exact le_csSup (hfin.bddAbove) ⟨(i, j), rfl⟩
  have hmaxM_pos : 0 < maxM := by
    have hmem : M ⟨0, hn⟩ ⟨0, hn⟩ ∈ Set.range (fun p : Fin n × Fin n => M p.1 p.2) := ⟨(⟨0, hn⟩, ⟨0, hn⟩), rfl⟩
    have : 0 < M ⟨0, hn⟩ ⟨0, hn⟩ := hpos ⟨0, hn⟩ ⟨0, hn⟩
    exact lt_of_lt_of_le this (le_csSup (hfin.bddAbove) hmem)
  -- Choose B = maxM
  use minM / ((n : ℝ) * maxM)
  use maxM
  refine ⟨?_, ?_, hmaxM_ub, ?_⟩
  · -- Show 0 < minM / (n * maxM)
    positivity
  · -- Show minM / (n * maxM) ≤ n⁻¹
    have h1 : minM ≤ maxM := by
      have hmem : M ⟨0, hn⟩ ⟨0, hn⟩ ∈ Set.range (fun p : Fin n × Fin n => M p.1 p.2) := ⟨(⟨0, hn⟩, ⟨0, hn⟩), rfl⟩
      exact le_trans (csInf_le hfin.bddBelow hmem) (le_csSup hfin.bddAbove hmem)
    calc minM / ((n : ℝ) * maxM) ≤ maxM / ((n : ℝ) * maxM) := by gcongr
      _ = (n : ℝ)⁻¹ := by field_simp
  · -- Show the normalized image is in Kset n δ
    intro x hx_nonneg hx_sum
    have hsum_pos : 0 < ∑ j, M.mulVec x j := by
      -- Since ∑ x = 1, there exists some k with x k > 0
      obtain ⟨k, hk⟩ : ∃ k, 0 < x k := by
        by_contra h
        push_neg at h
        have : ∑ i, x i ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
        linarith
      -- For any j, (M *ᵥ x) j ≥ M j k * x k > 0
      have hge : ∀ j, M.mulVec x j ≥ M j k * x k := by
        intro j
        simp [Matrix.mulVec]
        apply Finset.single_le_sum (fun i _ => mul_nonneg (le_of_lt (hpos j i)) (hx_nonneg i))
        simp
      have hpos_jk : 0 < M ⟨0, hn⟩ k * x k := mul_pos (hpos _ _) hk
      have hnonneg : ∀ j, 0 ≤ M.mulVec x j := fun j => by
        simp [Matrix.mulVec]
        apply Finset.sum_nonneg
        intro i _
        exact mul_nonneg (le_of_lt (hpos j i)) (hx_nonneg i)
      calc 0 < M (⟨0, hn⟩ : Fin n) k * x k := hpos_jk
        _ ≤ M.mulVec x (⟨0, hn⟩ : Fin n) := hge (⟨0, hn⟩ : Fin n)
        _ ≤ ∑ j, M.mulVec x j := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    constructor
    · -- Each coordinate ≥ δ
      intro i
      -- (M *ᵥ x) i ≥ minM
      have hnum : M.mulVec x i ≥ minM := by
        simp [Matrix.mulVec]
        calc minM = minM * ∑ j, x j := by rw [hx_sum, mul_one]
          _ = ∑ j, minM * x j := by rw [Finset.mul_sum]
          _ ≤ ∑ j, M i j * x j := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_right (csInf_le hfin.bddBelow ⟨(i, j), rfl⟩) (hx_nonneg j)
      -- ∑ j, (M *ᵥ x) j ≤ n * maxM
      have hdenom : ∑ j, M.mulVec x j ≤ (n : ℝ) * maxM := by
        simp only [Matrix.mulVec, dotProduct]
        calc ∑ j, ∑ k, M j k * x k ≤ ∑ j, ∑ k, maxM * x k := by
              apply Finset.sum_le_sum
              intro j _
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_right (hmaxM_ub j k) (hx_nonneg k)
          _ = ∑ _j : Fin n, maxM * 1 := by
              congr 1
              ext j
              rw [← Finset.mul_sum, hx_sum, mul_one]
          _ = n * maxM := by simp [mul_comm]
      -- So ratio ≥ minM / (n * maxM) = δ
      have hxi_nonneg : 0 ≤ (M *ᵥ x) i := by
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_nonneg fun j _ => mul_nonneg (hpos i j).le (hx_nonneg j)
      have hnpos : (0:ℝ) < (n : ℝ) * maxM := by positivity
      calc minM / ((n : ℝ) * maxM)
          ≤ (M *ᵥ x) i / ((n : ℝ) * maxM) := by gcongr
        _ ≤ (M *ᵥ x) i / (∑ j, M.mulVec x j) := by gcongr
    · -- Sum equals 1
      rw [← Finset.sum_div]
      rw [div_self (ne_of_gt hsum_pos)]

lemma exists_pos_ratio (hn : 0 < n) (hpos : ∀ i j, 0 < M i j) {δ : ℝ} (hδ : 0 < δ)
    {x : Fin n → ℝ} (hx : x ∈ Kset n δ) : ∃ t : ℝ, 0 < t ∧ ∀ i, t * x i ≤ M.mulVec x i := by
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le hδ (hx.1 i)
  have hxne : x ≠ 0 := Kset_ne_zero hx
  have hMxpos : ∀ i, 0 < M.mulVec x i :=
    fun i => mulVec_pos hpos (fun i => (hxpos i).le) hxne i
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne (fun i => M.mulVec x i / x i), ?_, fun i => ?_⟩
  · rw [Finset.lt_inf'_iff]
    exact fun i _ => div_pos (hMxpos i) (hxpos i)
  · have h : Finset.univ.inf' hne (fun i => M.mulVec x i / x i) ≤ M.mulVec x i / x i :=
      Finset.inf'_le _ (Finset.mem_univ i)
    rwa [le_div_iff₀ (hxpos i)] at h

/-- From a strict componentwise gap one extracts a uniform improvement `ε`. -/
lemma exists_eps_gap (hn : 0 < n) {r : ℝ} {u : Fin n → ℝ} (hu : ∀ i, 0 < u i)
    (hgap : ∀ i, r * u i < M.mulVec u i) :
    ∃ ε > 0, ∀ i, (r + ε) * u i ≤ M.mulVec u i := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  set e := fun i => (M.mulVec u i - r * u i) / u i with he
  have he_pos_all : ∀ i, 0 < e i := fun i => div_pos (sub_pos.mpr (hgap i)) (hu i)
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  refine ⟨e i₀, he_pos_all i₀, fun i => ?_⟩
  have h1 : e i₀ * u i ≤ e i * u i :=
    mul_le_mul_of_nonneg_right (hmin i (Finset.mem_univ i)) (hu i).le
  have h2 : e i * u i = M.mulVec u i - r * u i := div_mul_cancel₀ _ (ne_of_gt (hu i))
  nlinarith [h1, h2]

/-- If `M v ≥ r v` but `M v ≠ r v`, then the normalized image of `v` gives a strictly better
ratio. -/
lemma exists_improve (hn : 0 < n) (hpos : ∀ i j, 0 < M i j) {δ : ℝ} (hδ : 0 < δ)
    (hnorm : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
        (fun i => M.mulVec x i / ∑ j, M.mulVec x j) ∈ Kset n δ)
    {r : ℝ} {v : Fin n → ℝ} (hv : v ∈ Kset n δ)
    (hineq : ∀ i, r * v i ≤ M.mulVec v i) (hne : M.mulVec v ≠ r • v) :
    ∃ ε > 0, ∃ u ∈ Kset n δ, ∀ i, (r + ε) * u i ≤ M.mulVec u i := by
  -- v has all positive entries since v ∈ Kset n δ and δ > 0
  have hvpos : ∀ i, 0 < v i := fun i => lt_of_lt_of_le hδ (hv.1 i)
  -- Since M.mulVec v ≠ r • v and M.mulVec v ≥ r • v, there's a strict inequality somewhere
  have hstrict : ∃ i, r * v i < M.mulVec v i := by
    by_contra h
    push_neg at h
    exact hne (funext (fun i => le_antisymm (h i) (hineq i)))
  -- v ≠ 0
  have hv0 : v ≠ 0 := Kset_ne_zero hv
  -- M.mulVec v has all positive entries
  have hMvpos : ∀ i, 0 < M.mulVec v i := mulVec_pos hpos (fun i => le_of_lt (hvpos i)) hv0
  -- Define S = ∑ j, M.mulVec v j, which is positive
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set S := ∑ j, M.mulVec v j with hSdef
  have hSpos : 0 < S := Finset.sum_pos (fun _ _ => hMvpos _) Finset.univ_nonempty
  -- The normalized image w is in Kset n δ (using hnorm with v)
  have hwK : (fun i => M.mulVec v i / S) ∈ Kset n δ := hnorm v (fun i => le_of_lt (hvpos i)) hv.2
  -- M.mulVec (M.mulVec v) > r * M.mulVec v componentwise (strictly)
  have hM2v_strict_all : ∀ i, r * M.mulVec v i < M.mulVec (M.mulVec v) i := by
    intro i
    have hMv_i_pos := hMvpos i
    obtain ⟨k', hk'⟩ := hstrict
    have hSum_ge : ∑ j, M i j * M.mulVec v j > ∑ j, M i j * (r * v j) := by
      apply Finset.sum_lt_sum
      · intro j _
        apply mul_le_mul_of_nonneg_left (hineq j) (le_of_lt (hpos i j))
      · exact ⟨k', Finset.mem_univ k', mul_lt_mul_of_pos_left hk' (hpos i k')⟩
    have hSum_eq : ∑ j, M i j * (r * v j) = r * M.mulVec v i := by
      rw [Matrix.mulVec, dotProduct]
      have : ∑ j, M i j * (r * v j) = ∑ j, r * (M i j * v j) := by
        congr 1 with j; ring
      rw [this, ← Finset.mul_sum]
    have hM2v_i : M.mulVec (M.mulVec v) i = ∑ j, M i j * M.mulVec v j := rfl
    linarith
  -- Use exists_eps_gap to get uniform ε
  obtain ⟨ε, hεpos, hε⟩ := exists_eps_gap hn hMvpos hM2v_strict_all
  -- Now show (r + ε) * w i ≤ M.mulVec w i for w = M.mulVec v / S
  refine ⟨ε, hεpos, fun i => M.mulVec v i / S, hwK, ?_⟩
  intro i
  calc (r + ε) * (M.mulVec v i / S)
      = ((r + ε) * M.mulVec v i) / S := by ring
    _ ≤ (M.mulVec (M.mulVec v) i) / S := by gcongr; exact hε i
    _ = M.mulVec (fun j => M.mulVec v j / S) i := by
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_div]
        congr 1 with j
        rw [mul_div_assoc]

/-- Perron's theorem (positive case): a square matrix with strictly positive real entries has a
    positive real eigenvalue with a strictly positive eigenvector. -/
theorem perron (n : ℕ) (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (hpos : ∀ i j, 0 < M i j) :
    ∃ (l : ℝ) (v : Fin n → ℝ), 0 < l ∧ (∀ i, 0 < v i) ∧ M.mulVec v = l • v := by
  obtain ⟨δ, B, hδ, hδn, hB, hnorm⟩ := exists_delta hn hpos
  -- the uniform probability vector belongs to `Kset n δ`
  have hunif : (fun _ : Fin n => (n : ℝ)⁻¹) ∈ Kset n δ := by
    refine ⟨fun i => hδn, ?_⟩
    simp [Finset.card_univ]
    field_simp
  have hCne : (Cset M δ).Nonempty :=
    ⟨(0, fun _ => (n : ℝ)⁻¹), le_refl 0, hunif, by
      intro i
      have := mulVec_pos hpos (fun i => Kset_nonneg hδ.le hunif i) (Kset_ne_zero hunif) i
      simpa using this.le⟩
  have hCcomp : IsCompact (Cset M δ) := isCompact_Cset M hδ hB
  obtain ⟨p, hpC, hpmax⟩ := hCcomp.exists_isMaxOn hCne (continuous_fst.continuousOn)
  obtain ⟨hp0, hpK, hpineq⟩ := hpC
  set r := p.1 with hrdef
  set v := p.2 with hvdef
  -- `r` is positive
  have hrpos : 0 < r := by
    obtain ⟨t, ht0, ht⟩ := exists_pos_ratio hn hpos hδ hunif
    have : t ≤ r :=
      hpmax (show ((t, fun _ : Fin n => (n : ℝ)⁻¹) : ℝ × (Fin n → ℝ)) ∈ Cset M δ from
        ⟨ht0.le, hunif, ht⟩)
    linarith
  -- `M v = r v`
  have heq : M.mulVec v = r • v := by
    by_contra hne
    obtain ⟨ε, hε, u, huK, hu⟩ := exists_improve hn hpos hδ hnorm hpK hpineq hne
    have : r + ε ≤ r := hpmax (show ((r + ε, u) : ℝ × (Fin n → ℝ)) ∈ Cset M δ from
      ⟨by linarith, huK, hu⟩)
    linarith
  exact ⟨r, v, hrpos, fun i => lt_of_lt_of_le hδ (hpK.1 i), heq⟩

end Brockian.MsPerronFrobenius

