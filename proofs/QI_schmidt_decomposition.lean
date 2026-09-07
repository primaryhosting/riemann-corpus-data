import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Statement: Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Finset Matrix
open scoped ComplexConjugate InnerProductSpace

namespace QI

variable {m n : ℕ}

/-- `IsSchmidtDecomposition psi σ u v` says that the bipartite pure state `psi`, a vector of the
tensor product `ℂ^m ⊗ ℂ^n` realized as `EuclideanSpace ℂ (Fin m × Fin n)`, is written as
`psi = ∑ k, σ k • (u k ⊗ v k)` where the `σ k` are strictly positive reals (the Schmidt
coefficients) and `u`, `v` are orthonormal families in the two factors. -/
structure IsSchmidtDecomposition {ι : Type} [Fintype ι]
    (psi : EuclideanSpace ℂ (Fin m × Fin n)) (σ : ι → ℝ)
    (u : ι → EuclideanSpace ℂ (Fin m)) (v : ι → EuclideanSpace ℂ (Fin n)) : Prop where
  coeff_pos : ∀ k, 0 < σ k
  left_orthonormal : Orthonormal ℂ u
  right_orthonormal : Orthonormal ℂ v
  sum_eq : ∀ i j, psi (i, j) = ∑ k, (σ k : ℂ) * u k i * v k j

/-- The matrix of coefficients of a bipartite state in the product basis. -/
noncomputable def coeffMatrix (psi : EuclideanSpace ℂ (Fin m × Fin n)) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => psi (i, j)

/-- The (unnormalized) reduced density matrix of `psi` on the first factor. -/
noncomputable def reducedLeft (psi : EuclideanSpace ℂ (Fin m × Fin n)) : Matrix (Fin m) (Fin m) ℂ :=
  coeffMatrix psi * (coeffMatrix psi)ᴴ

lemma reducedLeft_apply (psi : EuclideanSpace ℂ (Fin m × Fin n)) (i a : Fin m) :
    reducedLeft psi i a = ∑ j, psi (i, j) * conj (psi (a, j)) := by
  simp [reducedLeft, coeffMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma reducedLeft_isHermitian (psi : EuclideanSpace ℂ (Fin m × Fin n)) :
    (reducedLeft psi).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self _

/-- The inner product on `EuclideanSpace` written as a sum of coordinates. -/
lemma inner_euclidean {N : ℕ} (x y : EuclideanSpace ℂ (Fin N)) :
    ⟪x, y⟫_ℂ = ∑ i, conj (x i) * y i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Resolution of the identity for an orthonormal basis of `EuclideanSpace ℂ (Fin m)`. -/
lemma sum_mul_conj_orthonormalBasis
    (w : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (i a : Fin m) :
    ∑ k, (w k) i * conj ((w k) a) = if i = a then 1 else 0 := by
  have h := w.sum_inner_mul_inner (EuclideanSpace.single i (1 : ℂ))
    (EuclideanSpace.single a (1 : ℂ))
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    EuclideanSpace.single_apply, eq_comm] using h

/-- Auxiliary vectors in the second factor: `y k` is the `k`-th row of the coefficient matrix
in the eigenbasis `w` of the reduced density matrix. -/
noncomputable def yvec (psi : EuclideanSpace ℂ (Fin m × Fin n))
    (w : Fin m → EuclideanSpace ℂ (Fin m)) (k : Fin m) : EuclideanSpace ℂ (Fin n) :=
  (WithLp.toLp 2 (fun j => ∑ a, conj (w k a) * psi (a, j)) : EuclideanSpace ℂ (Fin n))

@[simp] lemma yvec_apply (psi : EuclideanSpace ℂ (Fin m × Fin n))
    (w : Fin m → EuclideanSpace ℂ (Fin m)) (k : Fin m) (j : Fin n) :
    yvec psi w k j = ∑ a, conj (w k a) * psi (a, j) := rfl

section Aux

variable (psi : EuclideanSpace ℂ (Fin m × Fin n))

/-- Inner products of the auxiliary vectors, computed from the eigenvector equation. -/
lemma inner_yvec (w : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (lam : Fin m → ℝ)
    (hw : ∀ k, (reducedLeft psi) *ᵥ (w k).ofLp = lam k • (w k).ofLp) (k l : Fin m) :
    ⟪yvec psi (fun i => w i) k, yvec psi (fun i => w i) l⟫_ℂ =
      (lam k : ℂ) * (if l = k then 1 else 0) := by
  rw [inner_euclidean]
  have e1 : ∀ j : Fin n, conj (yvec psi (fun i => w i) k j) * yvec psi (fun i => w i) l j
      = ∑ b, ∑ a, (conj ((w l) b) * psi (b, j)) * ((w k) a * conj (psi (a, j))) := by
    intro j
    simp only [yvec_apply, map_sum, map_mul, Complex.conj_conj, ← Finset.sum_mul_sum]
    rw [mul_comm]
  simp only [e1]
  rw [Finset.sum_comm]
  have e2 : ∀ b : Fin m, ∑ j, ∑ a, (conj ((w l) b) * psi (b, j)) * ((w k) a * conj (psi (a, j)))
      = conj ((w l) b) * (((reducedLeft psi) *ᵥ (w k).ofLp) b) := by
    intro b
    rw [Finset.sum_comm]
    simp only [Matrix.mulVec, dotProduct, reducedLeft_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [e2, hw k]
  have h : ∑ b, conj ((w l) b) * (((lam k) • (w k).ofLp) b) = (lam k : ℂ) * ⟪w l, w k⟫_ℂ := by
    rw [inner_euclidean, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [Complex.real_smul]
    ring
  rw [h, orthonormal_iff_ite.mp w.orthonormal l k]

/-- Reconstruction of the coefficient matrix from an orthonormal eigenbasis. -/
lemma coeff_eq_sum_yvec (w : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (i : Fin m) (j : Fin n) :
    psi (i, j) = ∑ k, w k i * yvec psi (fun i => w i) k j := by
  have h : ∑ k, (w k) i * yvec psi (fun i => w i) k j
      = ∑ a, (∑ k, (w k) i * conj ((w k) a)) * psi (a, j) := by
    simp only [yvec_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h]
  simp [sum_mul_conj_orthonormalBasis w]

end Aux

/-- **Existence** of a Schmidt decomposition. -/
theorem exists_schmidtDecomposition (psi : EuclideanSpace ℂ (Fin m × Fin n)) :
    ∃ (r : ℕ) (σ : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
      (v : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomposition psi σ u v := by
  classical
  have hA : (reducedLeft psi).IsHermitian := reducedLeft_isHermitian psi
  set w := hA.eigenvectorBasis with hwdef
  set lam := hA.eigenvalues with hlamdef
  have hw : ∀ k, (reducedLeft psi) *ᵥ (w k).ofLp = lam k • (w k).ofLp :=
    fun k => hA.mulVec_eigenvectorBasis k
  set y : Fin m → EuclideanSpace ℂ (Fin n) := fun k => yvec psi (fun i => w i) k with hydef
  have hyy : ∀ k l, ⟪y k, y l⟫_ℂ = (lam k : ℂ) * (if l = k then 1 else 0) :=
    inner_yvec psi w lam hw
  have hself : ∀ k, ⟪y k, y k⟫_ℂ = (lam k : ℂ) := by
    intro k
    rw [hyy k k, if_pos rfl, mul_one]
  have hnn : ∀ k, 0 ≤ lam k := by
    intro k
    have h2 := inner_self_nonneg (𝕜 := ℂ) (x := y k)
    rw [hself k] at h2
    simpa using h2
  have hzero : ∀ k, lam k = 0 → y k = 0 := by
    intro k hk
    have h := hself k
    rw [hk] at h
    exact inner_self_eq_zero (𝕜 := ℂ) (x := y k) |>.mp (by simpa using h)
  set s : Finset (Fin m) := Finset.univ.filter (fun k => lam k ≠ 0) with hsdef
  set e : Fin s.card → Fin m := fun t => ((s.equivFin.symm t : {x // x ∈ s}) : Fin m) with hedef
  have hemem : ∀ t, e t ∈ s := fun t => (s.equivFin.symm t).2
  have hepos : ∀ t, 0 < lam (e t) := by
    intro t
    have h := hemem t
    rw [hsdef, Finset.mem_filter] at h
    exact lt_of_le_of_ne (hnn _) (Ne.symm h.2)
  have heinj : Function.Injective e :=
    Subtype.val_injective.comp s.equivFin.symm.injective
  have hsq : ∀ t, ((Real.sqrt (lam (e t)) : ℝ) : ℂ) ≠ 0 := by
    intro t
    simpa using (Real.sqrt_pos.mpr (hepos t)).ne'
  refine ⟨s.card, fun t => Real.sqrt (lam (e t)), fun t => w (e t),
    fun t => ((Real.sqrt (lam (e t)) : ℝ) : ℂ)⁻¹ • y (e t), ?_, ?_, ?_, ?_⟩
  · intro t; exact Real.sqrt_pos.mpr (hepos t)
  · exact w.orthonormal.comp e heinj
  · rw [orthonormal_iff_ite]
    intro t l
    rw [inner_smul_left, inner_smul_right, hyy]
    rcases eq_or_ne t l with rfl | htl
    · have h1 : ((Real.sqrt (lam (e t)) : ℝ) : ℂ) * ((Real.sqrt (lam (e t)) : ℝ) : ℂ)
          = (lam (e t) : ℂ) := by
        norm_cast
        exact Real.mul_self_sqrt (le_of_lt (hepos t))
      have hne := hsq t
      rw [if_pos rfl, map_inv₀, Complex.conj_ofReal, mul_one, if_pos rfl, ← h1]
      field_simp
    · rw [if_neg (fun h => htl (heinj h).symm), if_neg htl]
      ring
  · intro i j
    have h1 : psi (i, j) = ∑ k, w k i * y k j := coeff_eq_sum_yvec psi w i j
    have h2 : ∑ k, w k i * y k j = ∑ k ∈ s, w k i * y k j := by
      refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
      intro k _ hk
      have hk0 : lam k = 0 := by
        rw [hsdef, Finset.mem_filter] at hk
        by_contra hne
        exact hk ⟨Finset.mem_univ k, hne⟩
      rw [hzero k hk0]
      simp
    have h3 : ∑ k ∈ s, w k i * y k j = ∑ t : Fin s.card, w (e t) i * y (e t) j := by
      rw [← Finset.sum_coe_sort s (fun k => w k i * y k j)]
      exact (Equiv.sum_comp s.equivFin.symm (fun x : {x // x ∈ s} => w x i * y x j)).symm
    rw [h1, h2, h3]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [PiLp.smul_apply, smul_eq_mul]
    field_simp [hsq t]

section Uniqueness

variable {ι : Type} [Fintype ι] {psi : EuclideanSpace ℂ (Fin m × Fin n)} {σ : ι → ℝ}
  {u : ι → EuclideanSpace ℂ (Fin m)} {v : ι → EuclideanSpace ℂ (Fin n)}

/-- The reduced density matrix computed from a Schmidt decomposition. -/
lemma reducedLeft_of_schmidt (h : IsSchmidtDecomposition psi σ u v) (i a : Fin m) :
    reducedLeft psi i a = ∑ k, ((σ k ^ 2 : ℝ) : ℂ) * u k i * conj (u k a) := by
  classical
  have hv : ∀ k l, (∑ j, v k j * conj (v l j)) = if l = k then 1 else 0 := by
    intro k l
    have hkl := orthonormal_iff_ite.mp h.right_orthonormal l k
    rw [inner_euclidean] at hkl
    rw [← hkl]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [reducedLeft_apply]
  have step : ∀ j : Fin n, psi (i, j) * conj (psi (a, j))
      = ∑ k, ∑ l, ((σ k : ℂ) * u k i * ((σ l : ℂ) * conj (u l a))) * (v k j * conj (v l j)) := by
    intro j
    rw [h.sum_eq i j, h.sum_eq a j, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  simp only [step]
  have swap : ∑ j, ∑ k, ∑ l, ((σ k : ℂ) * u k i * ((σ l : ℂ) * conj (u l a)))
        * (v k j * conj (v l j))
      = ∑ k, ∑ l, ((σ k : ℂ) * u k i * ((σ l : ℂ) * conj (u l a)))
        * (∑ j, v k j * conj (v l j)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
  rw [swap]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hv]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
    push_cast
    ring
  · intro l _ hl
    rw [if_neg hl, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The operator associated with the reduced density matrix, in terms of a Schmidt
decomposition. -/
lemma toEuclideanLin_reducedLeft_of_schmidt (h : IsSchmidtDecomposition psi σ u v)
    (x : EuclideanSpace ℂ (Fin m)) :
    Matrix.toEuclideanLin (reducedLeft psi) x =
      ∑ k, ((σ k ^ 2 : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k) := by
  refine PiLp.ext fun i => ?_
  have hlhs : (Matrix.toEuclideanLin (reducedLeft psi) x) i = ∑ a, reducedLeft psi i a * x a := by
    simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  have hrhs : ((∑ k, ((σ k ^ 2 : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k) : EuclideanSpace ℂ (Fin m))) i
      = ∑ k, ((σ k ^ 2 : ℝ) : ℂ) * (⟪u k, x⟫_ℂ * u k i) := by
    simp
  rw [hlhs, hrhs]
  simp only [fun a => reducedLeft_of_schmidt h i a, inner_euclidean, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The eigenspace for a positive eigenvalue `t` of an operator given in "spectral" form
`T x = ∑ k, c k • ⟪u k, x⟫ • u k` with `u` orthonormal and `c` positive is spanned by the
`u k` with `c k = t`; in particular its dimension is the number of such `k`. -/
lemma finrank_eigenspace_of_spectral {c : ι → ℝ}
    (hu : Orthonormal ℂ u) (T : Module.End ℂ (EuclideanSpace ℂ (Fin m)))
    (hT : ∀ x, T x = ∑ k, ((c k : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k)) {t : ℝ} (ht : 0 < t) :
    Module.finrank ℂ (T.eigenspace ((t : ℝ) : ℂ)) = #{k | c k = t} := by
  classical
  have htne : ((t : ℝ) : ℂ) ≠ 0 := by simpa using ht.ne'
  have hTinner : ∀ (l : ι) (x : EuclideanSpace ℂ (Fin m)),
      ⟪u l, T x⟫_ℂ = (c l : ℂ) * ⟪u l, x⟫_ℂ := by
    intro l x
    rw [hT x, inner_sum, Finset.sum_eq_single l]
    · rw [inner_smul_right, inner_smul_right, orthonormal_iff_ite.mp hu l l, if_pos rfl]
      ring
    · intro b _ hb
      rw [inner_smul_right, inner_smul_right, orthonormal_iff_ite.mp hu l b, if_neg (Ne.symm hb)]
      ring
    · intro hl
      exact absurd (Finset.mem_univ l) hl
  have key : T.eigenspace ((t : ℝ) : ℂ)
      = Submodule.span ℂ (Set.range (fun k : {k : ι // c k = t} => u (k : ι))) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx
      have ha : ∀ l, c l ≠ t → ⟪u l, x⟫_ℂ = 0 := by
        intro l hl
        have h1 := hTinner l x
        rw [hx, inner_smul_right] at h1
        have h2 : ((c l : ℂ) - ((t : ℝ) : ℂ)) * ⟪u l, x⟫_ℂ = 0 := by linear_combination -h1
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd (Complex.ofReal_inj.mp (sub_eq_zero.mp h3)) hl
        · exact h3
      have h1 : x = ((t : ℝ) : ℂ)⁻¹ • ∑ k, ((c k : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k) := by
        rw [← hT x, hx, smul_smul, inv_mul_cancel₀ htne, one_smul]
      rw [Finset.smul_sum] at h1
      have h2 : (∑ k, ((t : ℝ) : ℂ)⁻¹ • (((c k : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k)))
          = ∑ k ∈ Finset.univ.filter (fun k => c k = t), ⟪u k, x⟫_ℂ • u k := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : c k = t
        · rw [if_pos hk, hk, smul_smul, inv_mul_cancel₀ htne, one_smul]
        · rw [if_neg hk, ha k hk, zero_smul, smul_zero, smul_zero]
      rw [h1.trans h2]
      refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨⟨k, (Finset.mem_filter.mp hk).2⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, hT, Finset.sum_eq_single (k : ι)]
      · rw [orthonormal_iff_ite.mp hu (k : ι) (k : ι), if_pos rfl, k.2, one_smul]
      · intro b _ hb
        rw [orthonormal_iff_ite.mp hu b (k : ι), if_neg hb, zero_smul, smul_zero]
      · intro hk
        exact absurd (Finset.mem_univ (k : ι)) hk
  have hli : LinearIndependent ℂ (fun k : {k : ι // c k = t} => u (k : ι)) :=
    (hu.comp _ Subtype.val_injective).linearIndependent
  rw [key, finrank_span_eq_card hli]
  simp [Fintype.card_subtype]

end Uniqueness

/-- **Uniqueness** of the Schmidt coefficients: any two Schmidt decompositions of the same state
have the same number of terms and the same multiset of Schmidt coefficients. -/
theorem schmidt_coefficients_unique {ι κ : Type} [Fintype ι] [Fintype κ]
    {psi : EuclideanSpace ℂ (Fin m × Fin n)} {σ : ι → ℝ}
    {u : ι → EuclideanSpace ℂ (Fin m)} {v : ι → EuclideanSpace ℂ (Fin n)} {τ : κ → ℝ}
    {u' : κ → EuclideanSpace ℂ (Fin m)} {v' : κ → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi σ u v) (h' : IsSchmidtDecomposition psi τ u' v') :
    (Finset.univ.val.map σ) = (Finset.univ.val.map τ) := by
  classical
  have hT1 : ∀ x, (Matrix.toEuclideanLin (reducedLeft psi)) x
      = ∑ k, ((σ k ^ 2 : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k) :=
    fun x => toEuclideanLin_reducedLeft_of_schmidt h x
  have hT2 : ∀ x, (Matrix.toEuclideanLin (reducedLeft psi)) x
      = ∑ k, ((τ k ^ 2 : ℝ) : ℂ) • (⟪u' k, x⟫_ℂ • u' k) :=
    fun x => toEuclideanLin_reducedLeft_of_schmidt h' x
  refine Multiset.ext.mpr fun a => ?_
  rcases le_or_gt a 0 with hle | hpos
  · have e1 : ∀ {J : Type} [Fintype J] (f : J → ℝ), (∀ k, 0 < f k) →
        Multiset.count a (Multiset.map f Finset.univ.val) = 0 := by
      intro J _ f hf
      refine Multiset.count_eq_zero.mpr ?_
      simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, not_exists]
      intro k hk
      exact absurd (hk ▸ hf k) (not_lt.mpr hle)
    rw [e1 σ h.coeff_pos, e1 τ h'.coeff_pos]
  · have c1 : ∀ {J : Type} [Fintype J] (f : J → ℝ), (∀ k, 0 < f k) →
        Multiset.count a (Multiset.map f Finset.univ.val) = #{k | f k ^ 2 = a ^ 2} := by
      intro J _ f hf
      rw [Multiset.count_map]
      have hfin : Finset.filter (fun k => a = f k) Finset.univ
          = Finset.filter (fun k => f k ^ 2 = a ^ 2) Finset.univ := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro rfl; ring
        · intro hk
          have := hf k
          nlinarith [sq_nonneg (f k - a), sq_nonneg (f k + a)]
      calc (Multiset.filter (fun k => a = f k) Finset.univ.val).card
          = #{k | a = f k} := rfl
        _ = #{k | f k ^ 2 = a ^ 2} := by rw [hfin]
    have ha2 : (0 : ℝ) < a ^ 2 := by positivity
    rw [c1 σ h.coeff_pos, c1 τ h'.coeff_pos,
      ← finrank_eigenspace_of_spectral h.left_orthonormal _ hT1 ha2,
      ← finrank_eigenspace_of_spectral h'.left_orthonormal _ hT2 ha2]

/-- **Schmidt decomposition.** Every bipartite pure state `psi ∈ ℂ^m ⊗ ℂ^n` admits a Schmidt
decomposition `psi = ∑ k, σ k • (u k ⊗ v k)` with positive Schmidt coefficients `σ k` and
orthonormal families `u`, `v`; moreover the Schmidt coefficients are unique: any two Schmidt
decompositions have the same multiset of coefficients (hence the same Schmidt rank). -/
theorem schmidt_decomposition (psi : EuclideanSpace ℂ (Fin m × Fin n)) :
    (∃ (r : ℕ) (σ : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
        (v : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomposition psi σ u v) ∧
      (∀ (r r' : ℕ) (σ : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
          (v : Fin r → EuclideanSpace ℂ (Fin n)) (τ : Fin r' → ℝ)
          (u' : Fin r' → EuclideanSpace ℂ (Fin m)) (v' : Fin r' → EuclideanSpace ℂ (Fin n)),
        IsSchmidtDecomposition psi σ u v → IsSchmidtDecomposition psi τ u' v' →
          r = r' ∧ (Finset.univ.val.map σ) = (Finset.univ.val.map τ)) := by
  refine ⟨exists_schmidtDecomposition psi, ?_⟩
  intro r r' σ u v τ u' v' h h'
  have hm := schmidt_coefficients_unique h h'
  refine ⟨?_, hm⟩
  have := congrArg Multiset.card hm
  simpa using this

end QI

