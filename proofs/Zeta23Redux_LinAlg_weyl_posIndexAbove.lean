import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The quadratic form `x ↦ Re ⟪x, A x⟫` attached to a complex matrix `A`,
seen as an operator on `EuclideanSpace ℂ (Fin d)`. -/
noncomputable def quadForm (A : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) : ℝ :=
  RCLike.re (inner ℂ x ((Matrix.toEuclideanLin A) x))

lemma toEuclideanLin_eigenvectorBasis {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (j : Fin d) :
    (Matrix.toEuclideanLin A) (hA.eigenvectorBasis j)
      = (hA.eigenvalues j : ℂ) • hA.eigenvectorBasis j := by
  have h := hA.mulVec_eigenvectorBasis j
  apply WithLp.ofLp_injective (p := 2)
  simp [Matrix.toEuclideanLin, h]

/-- Diagonalization of the quadratic form in the eigenbasis. -/
lemma quadForm_eq {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadForm A x = ∑ j, hA.eigenvalues j * ‖inner ℂ (hA.eigenvectorBasis j) x‖ ^ 2 := by
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hA
  have key : ∀ j, inner ℂ (hA.eigenvectorBasis j) ((Matrix.toEuclideanLin A) x)
      = (hA.eigenvalues j : ℂ) * inner ℂ (hA.eigenvectorBasis j) x := by
    intro j
    rw [← hsym, toEuclideanLin_eigenvectorBasis hA j, inner_smul_left]
    simp
  unfold quadForm
  rw [← (hA.eigenvectorBasis).sum_inner_mul_inner x ((Matrix.toEuclideanLin A) x), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j, show (inner ℂ x (hA.eigenvectorBasis j) : ℂ)
      = starRingEnd ℂ (inner ℂ (hA.eigenvectorBasis j) x) from (inner_conj_symm _ _).symm,
    show (starRingEnd ℂ) (inner ℂ (hA.eigenvectorBasis j) x)
        * ((hA.eigenvalues j : ℂ) * inner ℂ (hA.eigenvectorBasis j) x)
      = (hA.eigenvalues j : ℂ) * ((starRingEnd ℂ) (inner ℂ (hA.eigenvectorBasis j) x)
        * inner ℂ (hA.eigenvectorBasis j) x) by ring, RCLike.conj_mul]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_mul]

lemma quadForm_add (A B : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    quadForm (A + B) x = quadForm A x + quadForm B x := by
  simp [quadForm]

/-- If all eigenvalues of a Hermitian matrix are `≤ t`, its quadratic form is bounded by
`t ‖x‖²`. -/
lemma quadForm_le {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (t : ℝ)
    (h : ∀ i, hA.eigenvalues i ≤ t) (x : EuclideanSpace ℂ (Fin d)) :
    quadForm A x ≤ t * ‖x‖ ^ 2 := by
  rw [quadForm_eq hA, ← hA.eigenvectorBasis.sum_sq_norm_inner_right x, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (h j) (by positivity)

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
noncomputable def posIndex {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card

/-- The number of eigenvalues of a Hermitian matrix that are strictly above `theta`. -/
noncomputable def posIndexAbove {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (theta : ℝ) : ℕ :=
  (Finset.univ.filter fun i => theta < hA.eigenvalues i).card

/-- **Weyl monotonicity of the positive index**: if `A` and `E` are Hermitian and every
eigenvalue of `E` has absolute value at most `theta`, then the number of eigenvalues of
`A + E` strictly above `theta` is at most the number of strictly positive eigenvalues
of `A`. -/
theorem weyl_posIndexAbove {A E : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (hE : E.IsHermitian) (theta : ℝ) (hbound : ∀ i, |hE.eigenvalues i| ≤ theta) :
    posIndexAbove (hA.add hE) theta ≤ posIndex hA := by
  classical
  have hAE : (A + E).IsHermitian := hA.add hE
  set b := hA.eigenvectorBasis with hb
  set c := hAE.eigenvectorBasis with hc
  set P : Finset (Fin d) := Finset.univ.filter (fun i => 0 < hA.eigenvalues i) with hP
  set S : Finset (Fin d) := Finset.univ.filter (fun i => theta < hAE.eigenvalues i) with hS
  have horthc : ∀ j k : Fin d, inner ℂ (c j) (c k) = if j = k then (1 : ℂ) else 0 :=
    orthonormal_iff_ite.mp c.orthonormal
  set v : {i // i ∈ S} → ({j // j ∈ P} → ℂ) := fun i j => inner ℂ (b j) (c i) with hv
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set g' : Fin d → ℂ := fun j => if h : j ∈ S then g ⟨j, h⟩ else 0 with hg'
    set x : EuclideanSpace ℂ (Fin d) := ∑ j, g' j • c j with hxdef
    have hxsum : x = ∑ i : {i // i ∈ S}, g i • c i := by
      rw [hxdef, ← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by simp [hg', hj]),
        ← Finset.sum_coe_sort S (fun j => g' j • c j)]
      exact Finset.sum_congr rfl fun i _ => by simp [hg', i.2]
    have hcx : ∀ j : Fin d, inner ℂ (c j) x = g' j := by
      intro j
      simp [hxdef, horthc]
    have hbx : ∀ j : Fin d, j ∈ P → inner ℂ (b j) x = 0 := by
      intro j hj
      have h1 := congrFun hg ⟨j, hj⟩
      rw [hxsum]
      simp only [inner_sum, inner_smul_right]
      simpa [hv, Finset.sum_apply] using h1
    have hQA : quadForm A x ≤ 0 := by
      rw [quadForm_eq hA]
      refine Finset.sum_nonpos fun j _ => ?_
      by_cases hj : j ∈ P
      · rw [← hb, hbx j hj]
        simp
      · have hle : hA.eigenvalues j ≤ 0 := by
          by_contra hcon
          refine hj ?_
          simp only [hP, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, not_le.mp hcon⟩
        exact mul_nonpos_of_nonpos_of_nonneg hle (by positivity)
    have hQE : quadForm E x ≤ theta * ‖x‖ ^ 2 :=
      quadForm_le hE theta (fun i => (abs_le.1 (hbound i)).2) x
    have hnorm : ‖x‖ ^ 2 = ∑ j, ‖g' j‖ ^ 2 := by
      rw [← c.sum_sq_norm_inner_right x]
      exact Finset.sum_congr rfl fun j _ => by rw [hcx j]
    have hQAE : quadForm (A + E) x = ∑ j, hAE.eigenvalues j * ‖g' j‖ ^ 2 := by
      rw [quadForm_eq hAE]
      exact Finset.sum_congr rfl fun j _ => by rw [← hc, hcx j]
    have hkey : ∑ j, (hAE.eigenvalues j - theta) * ‖g' j‖ ^ 2 ≤ 0 := by
      have h1 : quadForm (A + E) x ≤ theta * ‖x‖ ^ 2 := by
        rw [quadForm_add]
        linarith
      rw [hQAE, hnorm, Finset.mul_sum] at h1
      have : ∑ j, (hAE.eigenvalues j - theta) * ‖g' j‖ ^ 2
          = (∑ j, hAE.eigenvalues j * ‖g' j‖ ^ 2) - ∑ j, theta * ‖g' j‖ ^ 2 := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      linarith
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin d)),
        0 ≤ (hAE.eigenvalues j - theta) * ‖g' j‖ ^ 2 := by
      intro j _
      by_cases hj : j ∈ S
      · have : theta < hAE.eigenvalues j := by simpa [hS] using hj
        exact mul_nonneg (by linarith) (by positivity)
      · simp [hg', hj]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp
      (le_antisymm hkey (Finset.sum_nonneg hnonneg))
    intro i
    have h1 := hzero i.1 (Finset.mem_univ _)
    have h2 : theta < hAE.eigenvalues i.1 := by
      have hi := i.2
      simp only [hS, Finset.mem_filter] at hi
      exact hi.2
    have h3 : ‖g' i.1‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · exact h
    have : g' i.1 = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
      simpa using this
    simpa [hg', i.2] using this
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at hcard
  simpa [posIndex, posIndexAbove, hP, hS] using hcard

end Zeta23Redux.LinAlg

-- Axiom check
#print axioms Zeta23Redux.LinAlg.weyl_posIndexAbove

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

