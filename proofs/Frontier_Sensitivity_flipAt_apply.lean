import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/
def adj {n : ℕ} (u v : Q n) : Prop :=
  (Finset.univ.filter (fun i => u i ≠ v i)).card = 1

instance {n : ℕ} : DecidableRel (@adj n) := fun u v => by
  unfold adj; infer_instance

/-- Degree of `v` inside a vertex set `H`. -/
def degIn {n : ℕ} (H : Finset (Q n)) (v : Q n) : ℕ :=
  (H.filter (fun u => adj u v)).card

/-! ### The signed adjacency matrix of the hypercube -/

/-- Flip the `k`-th coordinate of a vertex. -/
def flipAt {n : ℕ} (k : Fin n) (u : Q n) : Q n := Function.update u k (!u k)

/-- The sign attached to flipping coordinate `k` of `u`: `(-1)` to the power of the
number of `1`-coordinates of `u` in positions before `k`. -/
def eps {n : ℕ} (u : Q n) (k : Fin n) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => i < k), (if u i then (-1 : ℝ) else 1)

/-- Huang's signed adjacency matrix of the `n`-cube. -/
noncomputable def sgnAdj {n : ℕ} : Matrix (Q n) (Q n) ℝ :=
  Matrix.of fun u v => ∑ k : Fin n, if v = flipAt k u then eps u k else 0

/-! #### Basic properties of `flipAt` -/

lemma flipAt_apply {n : ℕ} (k i : Fin n) (u : Q n) :
    flipAt k u i = if i = k then !u i else u i := by
  unfold flipAt
  by_cases h : i = k
  · subst h; simp
  · simp [h]

lemma flipAt_apply_self {n : ℕ} (k : Fin n) (u : Q n) : flipAt k u k = !u k := by
  simp [flipAt_apply]

lemma flipAt_apply_of_ne {n : ℕ} {k i : Fin n} (u : Q n) (h : i ≠ k) :
    flipAt k u i = u i := by
  simp [flipAt_apply, h]

lemma flipAt_comm {n : ℕ} (k l : Fin n) (u : Q n) :
    flipAt l (flipAt k u) = flipAt k (flipAt l u) := by
  funext i
  simp only [flipAt_apply]
  split_ifs <;> simp_all

@[simp] lemma flipAt_flipAt {n : ℕ} (k : Fin n) (u : Q n) : flipAt k (flipAt k u) = u := by
  funext i
  simp only [flipAt_apply]
  split_ifs <;> simp_all

lemma flipAt_ne_self {n : ℕ} (k : Fin n) (u : Q n) : flipAt k u ≠ u := by
  intro h
  have h2 := congrFun h k
  rw [flipAt_apply_self] at h2
  cases hu : u k <;> rw [hu] at h2 <;> simp at h2

lemma flipAt_inj {n : ℕ} {k l : Fin n} {u : Q n} (h : flipAt k u = flipAt l u) : k = l := by
  by_contra hkl
  have h2 := congrFun h k
  simp only [flipAt_apply, if_neg hkl] at h2
  cases hu : u k <;> rw [hu] at h2 <;> simp at h2

/-! #### Basic properties of `eps` -/

lemma eps_mul_self {n : ℕ} (u : Q n) (k : Fin n) : eps u k * eps u k = 1 := by
  rw [eps, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one ?_
  intro i _
  by_cases h : u i <;> simp [h]

lemma abs_eps {n : ℕ} (u : Q n) (k : Fin n) : |eps u k| = 1 := by
  have h := eps_mul_self u k
  have h2 : |eps u k| * |eps u k| = 1 := by rw [← abs_mul, h]; simp
  nlinarith [abs_nonneg (eps u k)]

/-- Flipping the coordinate `k` does not change the sign associated with `l ≤ k`. -/
lemma eps_flipAt_of_le {n : ℕ} (u : Q n) {k l : Fin n} (h : l ≤ k) :
    eps (flipAt k u) l = eps u l := by
  refine Finset.prod_congr rfl ?_
  intro i hi
  simp only [Finset.mem_filter] at hi
  have hik : i ≠ k := ne_of_lt (lt_of_lt_of_le hi.2 h)
  rw [flipAt_apply_of_ne _ hik]

/-- Flipping a coordinate `k` before `l` flips the sign associated with `l`. -/
lemma eps_flipAt_of_lt {n : ℕ} (u : Q n) {k l : Fin n} (h : k < l) :
    eps (flipAt k u) l = - eps u l := by
  have hk : k ∈ Finset.univ.filter (fun i : Fin n => i < l) := by simp [h]
  rw [eps, eps, ← Finset.mul_prod_erase _ _ hk, ← Finset.mul_prod_erase _ _ hk]
  have hprod : ∏ i ∈ (Finset.univ.filter (fun i : Fin n => i < l)).erase k,
      (if flipAt k u i then (-1 : ℝ) else 1)
      = ∏ i ∈ (Finset.univ.filter (fun i : Fin n => i < l)).erase k,
        (if u i then (-1 : ℝ) else 1) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [flipAt_apply_of_ne _ (Finset.ne_of_mem_erase hi)]
  rw [hprod, flipAt_apply_self]
  cases hu : u k <;> simp

/-! #### Entries of the signed adjacency matrix -/

lemma sgnAdj_apply_flipAt {n : ℕ} (u : Q n) (k : Fin n) :
    sgnAdj u (flipAt k u) = eps u k := by
  rw [sgnAdj]
  simp only [Matrix.of_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    have h : flipAt k u ≠ flipAt l u := fun h => hl (flipAt_inj h.symm)
    simp [h]
  · intro h; exact absurd (Finset.mem_univ k) h

lemma sgnAdj_eq_zero_of_forall {n : ℕ} {u v : Q n} (h : ∀ k : Fin n, v ≠ flipAt k u) :
    sgnAdj u v = 0 := by
  rw [sgnAdj]
  simp only [Matrix.of_apply]
  exact Finset.sum_eq_zero fun k _ => by simp [h k]

lemma abs_sgnAdj_le_one {n : ℕ} (u v : Q n) : |sgnAdj u v| ≤ 1 := by
  by_cases h : ∃ k : Fin n, v = flipAt k u
  · obtain ⟨k, rfl⟩ := h
    rw [sgnAdj_apply_flipAt, abs_eps]
  · push_neg at h
    rw [sgnAdj_eq_zero_of_forall h]
    simp

lemma adj_flipAt {n : ℕ} (u : Q n) (k : Fin n) : adj (flipAt k u) u := by
  have h : (Finset.univ.filter (fun i => flipAt k u i ≠ u i)) = {k} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, flipAt_apply]
    by_cases h : i = k <;> simp [h]
  rw [adj, h, Finset.card_singleton]

/-- If the matrix entry is nonzero then the two vertices are adjacent. -/
lemma adj_of_sgnAdj_ne_zero {n : ℕ} {u v : Q n} (h : sgnAdj v u ≠ 0) : adj u v := by
  by_contra hadj
  refine h (sgnAdj_eq_zero_of_forall ?_)
  intro k hk
  exact hadj (hk ▸ adj_flipAt v k)

/-! #### The key matrix identity `A² = n • 1` -/

lemma sgnAdj_mul_self {n : ℕ} :
    (sgnAdj (n := n)) * (sgnAdj (n := n)) = (n : ℝ) • (1 : Matrix (Q n) (Q n) ℝ) := by
  ext u w
  rw [Matrix.mul_apply]
  have hstep1 : ∑ v : Q n, sgnAdj u v * sgnAdj v w
      = ∑ v ∈ Finset.image (fun k : Fin n => flipAt k u) Finset.univ, sgnAdj u v * sgnAdj v w := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro v _ hv
    have h : ∀ k : Fin n, v ≠ flipAt k u := by
      intro k hk
      exact hv (Finset.mem_image.2 ⟨k, Finset.mem_univ k, hk.symm⟩)
    rw [sgnAdj_eq_zero_of_forall h, zero_mul]
  have hstep2 : ∑ v ∈ Finset.image (fun k : Fin n => flipAt k u) Finset.univ,
      sgnAdj u v * sgnAdj v w
      = ∑ k : Fin n, eps u k * sgnAdj (flipAt k u) w := by
    rw [Finset.sum_image (by intro a _ b _ h; exact flipAt_inj h)]
    exact Finset.sum_congr rfl fun k _ => by rw [sgnAdj_apply_flipAt]
  rw [hstep1, hstep2]
  set F : Fin n × Fin n → ℝ := fun p =>
    if w = flipAt p.2 (flipAt p.1 u) then eps u p.1 * eps (flipAt p.1 u) p.2 else 0 with hF
  have hexp : ∑ k : Fin n, eps u k * sgnAdj (flipAt k u) w
      = ∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)), F p := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sgnAdj]
    simp only [Matrix.of_apply, Finset.mul_sum, hF]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [hexp, ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _),
    Finset.sum_diag]
  have hoff : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, F p = 0 := by
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · rintro ⟨k, l⟩ hp
      simp only [Finset.mem_offDiag] at hp
      have hkl : k ≠ l := hp.2.2
      simp only [hF]
      rw [flipAt_comm l k u]
      rcases lt_or_gt_of_ne hkl with h | h
      · rw [eps_flipAt_of_lt u h, eps_flipAt_of_le u (le_of_lt h)]
        split_ifs <;> ring
      · rw [eps_flipAt_of_lt u h, eps_flipAt_of_le u (le_of_lt h)]
        split_ifs <;> ring
    · rintro ⟨k, l⟩ hp _
      simp only [Finset.mem_offDiag] at hp
      simp only [ne_eq, Prod.mk.injEq, not_and]
      intro h
      exact absurd h.symm hp.2.2
    · rintro ⟨k, l⟩ hp
      simp only [Finset.mem_offDiag] at hp ⊢
      exact ⟨hp.2.1, hp.1, hp.2.2.symm⟩
    · rintro ⟨k, l⟩ _; rfl
  rw [hoff, add_zero]
  have hdiag : ∀ k : Fin n, F (k, k) = if w = u then (1 : ℝ) else 0 := by
    intro k
    simp only [hF, flipAt_flipAt, eps_flipAt_of_le u (le_refl k), eps_mul_self]
  simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · ring

/-! ### Linear algebra -/

lemma finrank_pi_cube (n : ℕ) : Module.finrank ℝ (Q n → ℝ) = 2 ^ n := by
  rw [Module.finrank_pi]
  simp

/-- Eigenspace of the signed adjacency matrix for the eigenvalue `c`. -/
noncomputable def eigsp {n : ℕ} (c : ℝ) : Submodule ℝ (Q n → ℝ) :=
  LinearMap.ker (Matrix.mulVecLin (sgnAdj (n := n)) - c • LinearMap.id)

lemma mem_eigsp_iff {n : ℕ} (c : ℝ) (y : Q n → ℝ) :
    y ∈ eigsp (n := n) c ↔ sgnAdj *ᵥ y = c • y := by
  simp [eigsp, LinearMap.mem_ker, sub_eq_zero]

/-- `A² = n • 1` in the form of an identity for matrix-vector products. -/
lemma sgnAdj_mulVec_sq {n : ℕ} (x : Q n → ℝ) :
    sgnAdj *ᵥ (sgnAdj *ᵥ x) = (n : ℝ) • x := by
  rw [Matrix.mulVec_mulVec, sgnAdj_mul_self]
  simp [Matrix.smul_mulVec]

/-- The two eigenspaces for `±√n` span everything. -/
lemma eigsp_sup_eigsp {n : ℕ} (hn : 0 < n) :
    (eigsp (n := n) (Real.sqrt n)) ⊔ (eigsp (n := n) (-Real.sqrt n)) = ⊤ := by
  set s := Real.sqrt n with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hs2 : s * s = (n : ℝ) := Real.mul_self_sqrt (by positivity)
  rw [eq_top_iff]
  intro x _
  rw [Submodule.mem_sup]
  refine ⟨(1/(2*s)) • (sgnAdj *ᵥ x + s • x), ?_, (1/(2*s)) • (s • x - sgnAdj *ᵥ x), ?_, ?_⟩
  · rw [mem_eigsp_iff, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      sgnAdj_mulVec_sq, ← hs2]
    match_scalars <;> field_simp
  · rw [mem_eigsp_iff, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul,
      sgnAdj_mulVec_sq, ← hs2]
    match_scalars <;> field_simp
  · rw [← smul_add]
    have h3 : sgnAdj *ᵥ x + s • x + (s • x - sgnAdj *ᵥ x) = (2*s) • x := by module
    rw [h3, smul_smul]
    field_simp
    exact one_smul _ x

/-- Support subspace of a vertex set: functions vanishing outside `H`. -/
noncomputable def suppSpace {n : ℕ} (H : Finset (Q n)) : Submodule ℝ (Q n → ℝ) :=
  LinearMap.ker (LinearMap.funLeft ℝ ℝ (fun v : {v : Q n // v ∉ H} => (v : Q n)))

lemma mem_suppSpace_iff {n : ℕ} (H : Finset (Q n)) (y : Q n → ℝ) :
    y ∈ suppSpace H ↔ ∀ v, v ∉ H → y v = 0 := by
  constructor
  · intro hy v hv
    exact congrFun hy ⟨v, hv⟩
  · intro hy
    funext v
    exact hy v.1 v.2

lemma finrank_suppSpace {n : ℕ} (H : Finset (Q n)) :
    H.card ≤ Module.finrank ℝ (suppSpace H) := by
  set L := LinearMap.funLeft ℝ ℝ (fun v : {v : Q n // v ∉ H} => (v : Q n)) with hL
  have hrk := LinearMap.finrank_range_add_finrank_ker L
  have hle : Module.finrank ℝ (LinearMap.range L)
      ≤ Module.finrank ℝ ({v : Q n // v ∉ H} → ℝ) := Submodule.finrank_le _
  have hcard : Module.finrank ℝ ({v : Q n // v ∉ H} → ℝ) = Hᶜ.card := by
    rw [Module.finrank_pi, Fintype.card_subtype]
    congr 1
    ext x
    simp
  have hcc : Hᶜ.card = 2 ^ n - H.card := by
    rw [Finset.card_compl]; simp
  have hHle : H.card ≤ 2 ^ n := by
    have h := Finset.card_le_univ H; simpa using h
  rw [finrank_pi_cube] at hrk
  show H.card ≤ Module.finrank ℝ (LinearMap.ker L)
  omega

/-- The core estimate: an eigenvector with eigenvalue of absolute value `√n`
supported on `H` forces a vertex of `H` of degree at least `√n`. -/
lemma exists_large_degree_of_eigenvector {n : ℕ} (H : Finset (Q n)) (c : ℝ)
    (hc : |c| = Real.sqrt n) (y : Q n → ℝ) (hy : y ≠ 0)
    (hAy : sgnAdj *ᵥ y = c • y) (hsupp : ∀ v, v ∉ H → y v = 0) :
    ∃ v ∈ H, Real.sqrt n ≤ (degIn H v : ℝ) := by
  obtain ⟨v, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Q n)) (fun v => |y v|)
    ⟨fun _ => false, Finset.mem_univ _⟩
  have hmax' : ∀ u, |y u| ≤ |y v| := fun u => hmax u (Finset.mem_univ u)
  have hyv : 0 < |y v| := by
    obtain ⟨u, hu⟩ := Function.ne_iff.1 hy
    exact lt_of_lt_of_le (abs_pos.2 hu) (hmax' u)
  have hvH : v ∈ H := by
    by_contra hv
    rw [hsupp v hv] at hyv
    simp at hyv
  refine ⟨v, hvH, ?_⟩
  set S := H.filter (fun u => adj u v) with hS
  have hrow : ∑ u : Q n, sgnAdj v u * y u = c * y v := by
    have h := congrFun hAy v
    simpa [Matrix.mulVec, dotProduct] using h
  have hsum : ∑ u : Q n, sgnAdj v u * y u = ∑ u ∈ S, sgnAdj v u * y u := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro u _ hu
    rw [hS] at hu
    simp only [Finset.mem_filter, not_and] at hu
    by_cases hH' : u ∈ H
    · have hnadj : ¬ adj u v := hu hH'
      have h0 : sgnAdj v u = 0 := by
        by_contra h0
        exact hnadj (adj_of_sgnAdj_ne_zero h0)
      rw [h0, zero_mul]
    · rw [hsupp u hH', mul_zero]
  have hbound : |c| * |y v| ≤ (S.card : ℝ) * |y v| := by
    calc |c| * |y v| = |c * y v| := (abs_mul _ _).symm
    _ = |∑ u ∈ S, sgnAdj v u * y u| := by rw [← hsum, hrow]
    _ ≤ ∑ u ∈ S, |sgnAdj v u * y u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ S, 1 * |y v| := by
        refine Finset.sum_le_sum fun u _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_sgnAdj_le_one v u) (hmax' u) (abs_nonneg _) zero_le_one
    _ = (S.card : ℝ) * |y v| := by rw [Finset.sum_const, nsmul_eq_mul, one_mul]
  rw [hc] at hbound
  have hfin := le_of_mul_le_mul_right
    (by linarith [hbound] : Real.sqrt n * |y v| ≤ (S.card : ℝ) * |y v|) hyv
  simpa [degIn, hS] using hfin

/-- Huang's Sensitivity Theorem (2019): every induced subgraph of the n-cube on more
    than half of its `2^n` vertices contains a vertex of degree at least `√n`. -/
theorem huang_sensitivity {n : ℕ} (hn : 0 < n) (H : Finset (Q n))
    (hH : 2 ^ (n - 1) + 1 ≤ H.card) :
    ∃ v ∈ H, Real.sqrt n ≤ (degIn H v : ℝ) := by
  -- the two eigenspaces together span the whole space, so one of them is big
  have hsup := eigsp_sup_eigsp (n := n) hn
  have hdim : 2 ^ n ≤ Module.finrank ℝ (eigsp (n := n) (Real.sqrt n))
      + Module.finrank ℝ (eigsp (n := n) (-Real.sqrt n)) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (eigsp (n := n) (Real.sqrt n)) (eigsp (n := n) (-Real.sqrt n))
    rw [hsup, finrank_top, finrank_pi_cube] at h
    omega
  have hhalf : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
    simp [pow_succ]
    ring
  -- pick an eigenvalue whose eigenspace has dimension at least `2 ^ (n-1)`
  obtain ⟨c, hc, hcdim⟩ : ∃ c : ℝ, |c| = Real.sqrt n ∧
      2 ^ (n - 1) ≤ Module.finrank ℝ (eigsp (n := n) c) := by
    have hnn : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    by_cases h : 2 ^ (n - 1) ≤ Module.finrank ℝ (eigsp (n := n) (Real.sqrt n))
    · exact ⟨Real.sqrt n, abs_of_nonneg hnn, h⟩
    · exact ⟨-Real.sqrt n, by rw [abs_neg, abs_of_nonneg hnn], by omega⟩
  -- intersect with the space of vectors supported on `H`
  have hW := finrank_suppSpace H
  have hinf := Submodule.finrank_sup_add_finrank_inf_eq (eigsp (n := n) c) (suppSpace H)
  have hsupple : Module.finrank ℝ ((eigsp (n := n) c) ⊔ (suppSpace H) : Submodule ℝ (Q n → ℝ))
      ≤ 2 ^ n := by
    have h := Submodule.finrank_le ((eigsp (n := n) c) ⊔ (suppSpace H))
    rwa [finrank_pi_cube] at h
  have hpos : 0 < Module.finrank ℝ ((eigsp (n := n) c) ⊓ (suppSpace H) : Submodule ℝ (Q n → ℝ)) := by
    omega
  have hne : ((eigsp (n := n) c) ⊓ (suppSpace H) : Submodule ℝ (Q n → ℝ)) ≠ ⊥ := by
    intro h
    rw [h] at hpos
    simp at hpos
  obtain ⟨y, hymem, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hymem
  exact exists_large_degree_of_eigenvector H c hc y hy0
    ((mem_eigsp_iff c y).1 hymem.1) ((mem_suppSpace_iff H y).1 hymem.2)

end Frontier.Sensitivity

