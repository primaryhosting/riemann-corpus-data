import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Finset Matrix ComplexConjugate

variable {m n : ℕ}

/-- The coefficient matrix of a bipartite vector `ψ ∈ ℂ^m ⊗ ℂ^n`, where the tensor product is
modelled as `EuclideanSpace ℂ (Fin m × Fin n)`. -/
noncomputable def coeffMatrix (ψ : EuclideanSpace ℂ (Fin m × Fin n)) :
    Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i j => ψ (i, j)

/-- The (unnormalised) reduced density matrix of `ψ` on the first factor. -/
noncomputable def rho (ψ : EuclideanSpace ℂ (Fin m × Fin n)) : Matrix (Fin m) (Fin m) ℂ :=
  coeffMatrix ψ * (coeffMatrix ψ)ᴴ

/-- `IsSchmidtDecomp ψ r σ e f` says that `ψ = ∑ k, σ k • (e k ⊗ f k)` is a Schmidt decomposition
of the bipartite vector `ψ`: the `σ k` are positive reals, and `e`, `f` are orthonormal families
in the two factors. -/
def IsSchmidtDecomp (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (r : ℕ) (σ : Fin r → ℝ)
    (e : Fin r → EuclideanSpace ℂ (Fin m)) (f : Fin r → EuclideanSpace ℂ (Fin n)) : Prop :=
  (∀ k, 0 < σ k) ∧ Orthonormal ℂ e ∧ Orthonormal ℂ f ∧
    ∀ (i : Fin m) (j : Fin n), ψ (i, j) = ∑ k, (σ k : ℂ) * e k i * f k j

lemma rho_apply (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (i i' : Fin m) :
    rho ψ i i' = ∑ j, ψ (i, j) * conj (ψ (i', j)) := by
  simp [rho, coeffMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma inner_eq_sum {N : ℕ} (x y : EuclideanSpace ℂ (Fin N)) :
    inner ℂ x y = ∑ i, conj (x i) * y i := by
  rw [PiLp.inner_apply]; simp [RCLike.inner_apply, mul_comm]

/-- Orthonormality of a family in coordinates. -/
lemma orth_sum {N r : ℕ} {g : Fin r → EuclideanSpace ℂ (Fin N)} (hg : Orthonormal ℂ g)
    (k l : Fin r) : ∑ j, g k j * conj (g l j) = if k = l then 1 else 0 := by
  have h1 := (orthonormal_iff_ite.mp hg) k l
  rw [inner_eq_sum] at h1
  have h2 := congrArg (starRingEnd ℂ) h1
  simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply] at h2
  rw [h2]
  by_cases h : k = l <;> simp [h]

/-- The reduced density matrix expressed through a Schmidt decomposition. -/
lemma rho_apply_of_decomp {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {σ : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) (i i' : Fin m) :
    rho ψ i i' = ∑ k, ((σ k ^ 2 : ℝ) : ℂ) * e k i * conj (e k i') := by
  obtain ⟨hpos, he, hf, hdec⟩ := h
  rw [rho_apply]
  have key : ∀ j : Fin n, ψ (i, j) * conj (ψ (i', j))
      = ∑ k, ∑ l, ((σ k : ℂ) * e k i * ((σ l : ℂ) * conj (e l i'))) * (f k j * conj (f l j)) := by
    intro j
    rw [hdec i j, hdec i' j, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have hsum : ∀ l : Fin r,
      ∑ j, ((σ k : ℂ) * e k i * ((σ l : ℂ) * conj (e l i'))) * (f k j * conj (f l j))
        = ((σ k : ℂ) * e k i * ((σ l : ℂ) * conj (e l i'))) * (if k = l then 1 else 0) := by
    intro l
    rw [← Finset.mul_sum, orth_sum hf]
  simp only [hsum]
  simp [Finset.sum_ite_eq]
  ring

/-- The action of the reduced density matrix, expressed through a Schmidt decomposition. -/
lemma toEuclideanLin_rho_of_decomp {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {σ : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) (v : EuclideanSpace ℂ (Fin m)) :
    Matrix.toEuclideanLin (rho ψ) v = ∑ k, (((σ k ^ 2 : ℝ) : ℂ) * inner ℂ (e k) v) • e k := by
  ext i
  have hL : Matrix.toEuclideanLin (rho ψ) v i = ∑ i', rho ψ i i' * v i' := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [hL]
  have hR : (∑ k, (((σ k ^ 2 : ℝ) : ℂ) * inner ℂ (e k) v) • e k) i
      = ∑ k, (((σ k ^ 2 : ℝ) : ℂ) * inner ℂ (e k) v) * e k i := by
    simp
  rw [hR]
  simp only [rho_apply_of_decomp h, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  ring

/-- The eigenspace of the reduced density matrix for a nonzero eigenvalue `t` is spanned by the
Schmidt vectors whose squared coefficient equals `t`. -/
lemma eigenspace_eq_span {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {σ : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) {t : ℝ} (ht : t ≠ 0) :
    Module.End.eigenspace (Matrix.toEuclideanLin (rho ψ)) (t : ℂ) =
      Submodule.span ℂ (Set.range (fun k : {k : Fin r // σ k ^ 2 = t} => e (k : Fin r))) := by
  have he : Orthonormal ℂ e := h.2.1
  have hip : ∀ (l k : Fin r), (inner ℂ (e l) (e k) : ℂ) = if l = k then 1 else 0 :=
    orthonormal_iff_ite.mp he
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  apply le_antisymm
  · intro v hv
    rw [Module.End.mem_eigenspace_iff, toEuclideanLin_rho_of_decomp h v] at hv
    set c : Fin r → ℂ := fun k => inner ℂ (e k) v with hc
    have hkey : ∀ l : Fin r, ((σ l ^ 2 : ℝ) : ℂ) * c l = (t : ℂ) * c l := by
      intro l
      have h1 := congrArg (fun w => (inner ℂ (e l) w : ℂ)) hv
      simp only [inner_sum, inner_smul_right, hip, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
      simpa [hc] using h1
    have hzero : ∀ l : Fin r, σ l ^ 2 ≠ t → c l = 0 := by
      intro l hl
      have h1 := hkey l
      have h2 : (((σ l ^ 2 : ℝ) : ℂ) - (t : ℂ)) * c l = 0 := by ring_nf; linear_combination h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd (by exact_mod_cast sub_eq_zero.mp h3) hl
      · exact h3
    have hsum : (t : ℂ) • v =
        (t : ℂ) • ∑ k ∈ Finset.univ.filter (fun k : Fin r => σ k ^ 2 = t), c k • e k := by
      rw [← hv, Finset.smul_sum]
      rw [← Finset.sum_filter_of_ne (p := fun k : Fin r => σ k ^ 2 = t)]
      · refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_filter] at hk
        rw [hk.2, smul_smul]
      · intro k _ hk
        by_contra hne
        exact hk (by
          rw [show (inner ℂ (e k) v : ℂ) = 0 from hzero k hne, mul_zero, zero_smul])
    have hv' : v = ∑ k ∈ Finset.univ.filter (fun k : Fin r => σ k ^ 2 = t), c k • e k :=
      smul_right_injective _ htC hsum
    rw [hv']
    refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
    rw [Finset.mem_filter] at hk
    exact Submodule.subset_span ⟨⟨k, hk.2⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, toEuclideanLin_rho_of_decomp h]
    simp only [hip, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro l _ hl
      simp [hl]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'

lemma finrank_eigenspace_of_decomp {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {σ : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) {t : ℝ} (ht : t ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toEuclideanLin (rho ψ)) (t : ℂ)) =
      (Finset.univ.filter (fun k : Fin r => σ k ^ 2 = t)).card := by
  rw [eigenspace_eq_span h ht]
  have hli : LinearIndependent ℂ (fun k : {k : Fin r // σ k ^ 2 = t} => e (k : Fin r)) :=
    (h.2.1.comp _ Subtype.val_injective).linearIndependent
  rw [finrank_span_eq_card hli, Fintype.card_subtype]

/-- Two Schmidt decompositions of the same vector have the same number of coefficients with any
prescribed value. -/
lemma card_filter_eq {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r r' : ℕ} {σ : Fin r → ℝ}
    {σ' : Fin r' → ℝ} {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    {e' : Fin r' → EuclideanSpace ℂ (Fin m)} {f' : Fin r' → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) (h' : IsSchmidtDecomp ψ r' σ' e' f') (t : ℝ) :
    (Finset.univ.filter (fun k : Fin r => σ k = t)).card =
      (Finset.univ.filter (fun k : Fin r' => σ' k = t)).card := by
  rcases le_or_gt t 0 with hle | hpos
  · have e1 : (Finset.univ.filter (fun k : Fin r => σ k = t)) = ∅ := by
      refine Finset.filter_false_of_mem fun k _ hk => ?_
      exact absurd (hk ▸ h.1 k) (not_lt.mpr hle)
    have e2 : (Finset.univ.filter (fun k : Fin r' => σ' k = t)) = ∅ := by
      refine Finset.filter_false_of_mem fun k _ hk => ?_
      exact absurd (hk ▸ h'.1 k) (not_lt.mpr hle)
    rw [e1, e2, Finset.card_empty, Finset.card_empty]
  · have hsq : ∀ (s : ℝ), 0 < s → (s ^ 2 = t ^ 2 ↔ s = t) := by
      intro s hs
      constructor
      · intro hst; nlinarith
      · intro hst; rw [hst]
    have e1 : (Finset.univ.filter (fun k : Fin r => σ k = t))
        = (Finset.univ.filter (fun k : Fin r => σ k ^ 2 = t ^ 2)) := by
      refine Finset.filter_congr fun k _ => ?_
      simp [hsq (σ k) (h.1 k)]
    have e2 : (Finset.univ.filter (fun k : Fin r' => σ' k = t))
        = (Finset.univ.filter (fun k : Fin r' => σ' k ^ 2 = t ^ 2)) := by
      refine Finset.filter_congr fun k _ => ?_
      simp [hsq (σ' k) (h'.1 k)]
    have ht2 : t ^ 2 ≠ 0 := by positivity
    rw [e1, e2, ← finrank_eigenspace_of_decomp h ht2, ← finrank_eigenspace_of_decomp h' ht2]

/-- Uniqueness of the Schmidt coefficients (listed in decreasing order). -/
lemma schmidt_coeff_unique {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r r' : ℕ} {σ : Fin r → ℝ}
    {σ' : Fin r' → ℝ} {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    {e' : Fin r' → EuclideanSpace ℂ (Fin m)} {f' : Fin r' → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) (h' : IsSchmidtDecomp ψ r' σ' e' f')
    (ha : Antitone σ) (ha' : Antitone σ') :
    ∃ hr : r = r', ∀ k : Fin r, σ k = σ' (Fin.cast hr k) := by
  have hc := card_filter_eq h h'
  have hms : Multiset.map σ Finset.univ.val = Multiset.map σ' Finset.univ.val := by
    ext a
    rw [Multiset.count_map, Multiset.count_map]
    have e1 : (Multiset.filter (fun k : Fin r => a = σ k) Finset.univ.val).card
        = (Finset.univ.filter (fun k : Fin r => σ k = a)).card := by
      simp [Finset.filter, Finset.card, eq_comm]
    have e2 : (Multiset.filter (fun k : Fin r' => a = σ' k) Finset.univ.val).card
        = (Finset.univ.filter (fun k : Fin r' => σ' k = a)).card := by
      simp [Finset.filter, Finset.card, eq_comm]
    rw [e1, e2, hc a]
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at hms
  have hlen : r = r' := by simpa using hms.length_eq
  subst hlen
  have hsorted : ∀ (s : Fin r → ℝ), Antitone s → List.Pairwise (· ≥ ·) (List.ofFn s) := by
    intro s hs
    rw [List.pairwise_ofFn]
    exact fun i j hij => hs hij.le
  have hL : List.ofFn σ = List.ofFn σ' :=
    List.Perm.eq_of_pairwise (le := (· ≥ ·)) (fun a b _ _ h1 h2 => le_antisymm h2 h1)
      (hsorted σ ha) (hsorted σ' ha') hms
  refine ⟨rfl, fun k => ?_⟩
  have h2 : (List.ofFn σ)[(k : ℕ)]? = (List.ofFn σ')[(k : ℕ)]? := by rw [hL]
  simpa [List.getElem?_ofFn, k.isLt] using h2

private lemma sum_comm3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (F : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c := by
  rw [Finset.sum_comm]
  rw [show (∑ b, ∑ a, ∑ c, F a b c) = ∑ b, ∑ c, ∑ a, F a b c from
    Finset.sum_congr rfl fun b _ => Finset.sum_comm]
  exact Finset.sum_comm

/-- Existence of a Schmidt decomposition (coefficients not yet ordered).  This is the singular
value decomposition of the coefficient matrix, obtained from the spectral decomposition of the
reduced density matrix. -/
lemma exists_isSchmidtDecomp (ψ : EuclideanSpace ℂ (Fin m × Fin n)) :
    ∃ (r : ℕ) (σ : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
      (f : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomp ψ r σ e f := by
  classical
  have hH : (rho ψ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self _
  set u : Fin m → EuclideanSpace ℂ (Fin m) := fun a => hH.eigenvectorBasis a with hu
  set μ : Fin m → ℝ := hH.eigenvalues with hmu
  have hun : Orthonormal ℂ u := hH.eigenvectorBasis.orthonormal
  have hip : ∀ b a : Fin m, (inner ℂ (u b) (u a) : ℂ) = if b = a then 1 else 0 :=
    orthonormal_iff_ite.mp hun
  have hcomplete : ∀ i i' : Fin m, ∑ a, u a i * conj (u a i') = if i = i' then 1 else 0 := by
    intro i i'
    have h1 : (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
        star (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 := Unitary.coe_mul_star_self _
    have h2 := congrFun (congrFun h1 i) i'
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, hu] using h2
  have heig : ∀ (a i : Fin m), ∑ i', rho ψ i i' * u a i' = (μ a : ℂ) * u a i := by
    intro a i
    have h1 := congrFun (hH.mulVec_eigenvectorBasis a) i
    simpa [Matrix.mulVec, dotProduct, hu, hmu] using h1
  set w : Fin m → EuclideanSpace ℂ (Fin n) :=
    fun a => WithLp.toLp 2 (fun j => ∑ i', conj (u a i') * ψ (i', j)) with hw
  have hwapp : ∀ (a : Fin m) (j : Fin n), w a j = ∑ i', conj (u a i') * ψ (i', j) := by
    intro a j; simp [hw]
  have hexpand : ∀ a b : Fin m, (inner ℂ (w a) (w b) : ℂ)
      = ∑ i'', conj (u b i'') * (∑ i', rho ψ i'' i' * u a i') := by
    intro a b
    rw [inner_eq_sum]
    have step1 : ∀ j, conj (w a j) * w b j
        = ∑ i', ∑ i'', (u a i' * conj (ψ (i', j))) * (conj (u b i'') * ψ (i'', j)) := by
      intro j
      rw [hwapp, hwapp, map_sum]
      simp only [map_mul, Complex.conj_conj]
      rw [Finset.sum_mul_sum]
    simp only [step1]
    rw [sum_comm3 (fun j i' i'' => (u a i' * conj (ψ (i', j))) * (conj (u b i'') * ψ (i'', j)))]
    refine Finset.sum_congr rfl fun i'' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [rho_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hinner : ∀ a b : Fin m, (inner ℂ (w a) (w b) : ℂ) = if b = a then (μ a : ℂ) else 0 := by
    intro a b
    rw [hexpand a b]
    simp only [heig]
    have hfac : ∑ i'', conj (u b i'') * ((μ a : ℂ) * u a i'')
        = (μ a : ℂ) * ∑ i'', conj (u b i'') * u a i'' := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i'' _ => by ring
    rw [hfac, ← inner_eq_sum, hip b a]
    by_cases hba : b = a <;> simp [hba]
  have hmnorm : ∀ a, μ a = ‖w a‖ ^ 2 := by
    intro a
    have h1 : (inner ℂ (w a) (w a) : ℂ) = ((‖w a‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [hinner a a, if_pos rfl] at h1
    exact_mod_cast h1
  have hwzero : ∀ a, μ a = 0 → w a = 0 := by
    intro a ha
    have hn : ‖w a‖ = 0 := by
      have := hmnorm a
      nlinarith [norm_nonneg (w a)]
    exact norm_eq_zero.mp hn
  have hnonneg : ∀ a, 0 ≤ μ a := fun a => by rw [hmnorm a]; positivity
  have hrecon : ∀ (i : Fin m) (j : Fin n), ψ (i, j) = ∑ a, u a i * w a j := by
    intro i j
    have hterm : ∀ a, u a i * w a j = ∑ i', (u a i * conj (u a i')) * ψ (i', j) := by
      intro a
      rw [hwapp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i' _ => by ring
    simp only [hterm]
    rw [Finset.sum_comm]
    have hterm2 : ∀ i' : Fin m, ∑ a, (u a i * conj (u a i')) * ψ (i', j)
        = (if i = i' then 1 else 0) * ψ (i', j) := by
      intro i'
      rw [← Finset.sum_mul, hcomplete i i']
    simp only [hterm2]
    simp
  -- the indices carrying a positive eigenvalue
  set S : Finset (Fin m) := Finset.univ.filter (fun a => 0 < μ a) with hS
  set ι : Fin S.card → Fin m := fun k => ((S.equivFin.symm k : {x // x ∈ S}) : Fin m) with hι
  have hιmem : ∀ k, ι k ∈ S := fun k => (S.equivFin.symm k).2
  have hιpos : ∀ k, 0 < μ (ι k) := by
    intro k
    have hk := hιmem k
    rw [hS, Finset.mem_filter] at hk
    exact hk.2
  have hιinj : Function.Injective ι := Subtype.val_injective.comp S.equivFin.symm.injective
  have hreindex : ∀ g : Fin m → ℂ, ∑ k, g (ι k) = ∑ a ∈ S, g a := by
    intro g
    rw [← Finset.sum_coe_sort S g]
    exact Equiv.sum_comp S.equivFin.symm (fun x : {x // x ∈ S} => g x)
  have hcne : ∀ k, ((Real.sqrt (μ (ι k)) : ℝ) : ℂ) ≠ 0 := by
    intro k
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (hιpos k))
  refine ⟨S.card, fun k => Real.sqrt (μ (ι k)), fun k => u (ι k),
    fun k => (((Real.sqrt (μ (ι k)) : ℝ) : ℂ))⁻¹ • w (ι k),
    fun k => Real.sqrt_pos.mpr (hιpos k), hun.comp ι hιinj, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro k l
    rw [inner_smul_left, inner_smul_right, hinner (ι k) (ι l)]
    by_cases hkl : k = l
    · subst hkl
      have hsq : Real.sqrt (μ (ι k)) * Real.sqrt (μ (ι k)) = μ (ι k) :=
        Real.mul_self_sqrt (le_of_lt (hιpos k))
      have hcast : ((μ (ι k) : ℝ) : ℂ)
          = ((Real.sqrt (μ (ι k)) : ℝ) : ℂ) * ((Real.sqrt (μ (ι k)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, hsq]
      rw [if_pos rfl, if_pos rfl, hcast, map_inv₀, Complex.conj_ofReal]
      field_simp
      exact div_self (hcne k)
    · rw [if_neg hkl, if_neg (fun hc => hkl (hιinj hc).symm)]
      ring
  · intro i j
    have hcancel : ∀ k, ((Real.sqrt (μ (ι k)) : ℝ) : ℂ) * u (ι k) i
        * ((((Real.sqrt (μ (ι k)) : ℝ) : ℂ))⁻¹ • w (ι k)) j = u (ι k) i * w (ι k) j := by
      intro k
      have hsmul : ((((Real.sqrt (μ (ι k)) : ℝ) : ℂ))⁻¹ • w (ι k)) j
          = (((Real.sqrt (μ (ι k)) : ℝ) : ℂ))⁻¹ * w (ι k) j := by simp
      rw [hsmul]
      have := hcne k
      field_simp
    simp only [hcancel]
    rw [hreindex (fun a => u a i * w a j), hrecon i j]
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro a _ haS
    have hza : μ a = 0 := by
      rw [hS, Finset.mem_filter] at haS
      simp only [Finset.mem_univ, true_and, not_lt] at haS
      have := hnonneg a
      linarith
    rw [hwzero a hza]
    simp

/-- The Schmidt coefficients can always be sorted in decreasing order. -/
lemma exists_antitone_isSchmidtDecomp {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ}
    {σ : Fin r → ℝ} {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) :
    ∃ (σ' : Fin r → ℝ) (e' : Fin r → EuclideanSpace ℂ (Fin m))
      (f' : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomp ψ r σ' e' f' ∧ Antitone σ' := by
  obtain ⟨hpos, he, hf, hdec⟩ := h
  set p : Equiv.Perm (Fin r) := Tuple.sort (fun k => -σ k) with hp
  have hmono : Monotone ((fun k => -σ k) ∘ p) := Tuple.monotone_sort (fun k => -σ k)
  refine ⟨σ ∘ p, e ∘ p, f ∘ p, ⟨fun k => hpos _, he.comp p p.injective, hf.comp p p.injective,
    fun i j => ?_⟩, ?_⟩
  · rw [hdec i j]
    exact (Equiv.sum_comp p (fun k => (σ k : ℂ) * e k i * f k j)).symm
  · intro a b hab
    have := hmono hab
    simpa using neg_le_neg_iff.mp (by simpa using this)

/-- The squared Schmidt coefficients sum to the squared norm of the state. -/
lemma sum_sq_eq_norm_sq {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {σ : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) : ∑ k, σ k ^ 2 = ‖ψ‖ ^ 2 := by
  obtain ⟨hpos, he, hf, hdec⟩ := h
  have hone : ∀ k, ∑ i, ((σ k ^ 2 : ℝ) : ℂ) * e k i * conj (e k i) = ((σ k ^ 2 : ℝ) : ℂ) := by
    intro k
    have hk : ∑ i, e k i * conj (e k i) = 1 := by simpa using orth_sum he k k
    calc ∑ i, ((σ k ^ 2 : ℝ) : ℂ) * e k i * conj (e k i)
        = ((σ k ^ 2 : ℝ) : ℂ) * ∑ i, e k i * conj (e k i) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = ((σ k ^ 2 : ℝ) : ℂ) := by rw [hk, mul_one]
  have h1 : ∑ i, rho ψ i i = ((∑ k, σ k ^ 2 : ℝ) : ℂ) := by
    simp only [rho_apply_of_decomp ⟨hpos, he, hf, hdec⟩]
    rw [Finset.sum_comm, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ => hone k
  have h2 : ∑ i, rho ψ i i = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    simp only [rho_apply]
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    push_cast
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq _
  exact_mod_cast h1.symm.trans h2

/-- **Schmidt decomposition.**  Every bipartite pure state `ψ` in `ℂ^m ⊗ ℂ^n` (modelled as
`EuclideanSpace ℂ (Fin m × Fin n)`) can be written as `ψ = ∑ k, σ k • (e k ⊗ f k)` for a positive,
decreasing family of real Schmidt coefficients `σ` and orthonormal families `e`, `f` in the two
factors; the squared coefficients sum to `1`.  Moreover the Schmidt coefficients are unique: any
two such decompositions have the same number of terms and the same (decreasingly ordered)
coefficients. -/
theorem schmidt_decomposition (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (hψ : ‖ψ‖ = 1) :
    (∃ (r : ℕ) (σ : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
        (f : Fin r → EuclideanSpace ℂ (Fin n)),
        IsSchmidtDecomp ψ r σ e f ∧ Antitone σ ∧ ∑ k, σ k ^ 2 = 1) ∧
      (∀ (r r' : ℕ) (σ : Fin r → ℝ) (σ' : Fin r' → ℝ)
        (e : Fin r → EuclideanSpace ℂ (Fin m)) (f : Fin r → EuclideanSpace ℂ (Fin n))
        (e' : Fin r' → EuclideanSpace ℂ (Fin m)) (f' : Fin r' → EuclideanSpace ℂ (Fin n)),
        IsSchmidtDecomp ψ r σ e f → Antitone σ → IsSchmidtDecomp ψ r' σ' e' f' → Antitone σ' →
        ∃ hr : r = r', ∀ k : Fin r, σ k = σ' (Fin.cast hr k)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, σ₀, e₀, f₀, h₀⟩ := exists_isSchmidtDecomp ψ
    obtain ⟨σ, e, f, h, hanti⟩ := exists_antitone_isSchmidtDecomp h₀
    exact ⟨r, σ, e, f, h, hanti, by rw [sum_sq_eq_norm_sq h, hψ, one_pow]⟩
  · intro r r' σ σ' e f e' f' h ha h' ha'
    exact schmidt_coeff_unique h h' ha ha'

end QI

