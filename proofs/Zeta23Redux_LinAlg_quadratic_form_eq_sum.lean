/-
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix

/-- The positive index of a Hermitian matrix: the number of its strictly positive eigenvalues
(counted with multiplicity, i.e. as a number of indices).  For matrices that are not Hermitian
the value is set to `0`. -/
noncomputable def posIndex {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℕ :=
  if hA : A.IsHermitian then Nat.card {i : Fin d // 0 < hA.eigenvalues i} else 0

/-- Diagonalisation of the Hermitian form: in the coordinates given by the eigenvector unitary,
`x ↦ Re (star x ⬝ᵥ A *ᵥ x)` becomes `∑ i, eigenvalue i * ‖coordinate i‖²`. -/
lemma quadratic_form_eq_sum {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re =
      ∑ i, hA.eigenvalues i *
        Complex.normSq (((star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x) i) := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set lam : Fin d → ℝ := hA.eigenvalues with hlam
  set y : Fin d → ℂ := star U *ᵥ x with hy
  have hAeq : A = U * (diagonal (RCLike.ofReal ∘ lam)) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have h1 : A *ᵥ x = U *ᵥ ((diagonal (RCLike.ofReal ∘ lam)) *ᵥ y) := by
    rw [hAeq, hy, ← mulVec_mulVec, ← mulVec_mulVec]
  have h2 : star x ᵥ* U = star y := by
    rw [hy, star_mulVec, ← Matrix.star_eq_conjTranspose, star_star]
  rw [h1, dotProduct_mulVec, h2, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mulVec_diagonal, Complex.normSq_apply]
  ring

/-- **Sylvester's law of inertia** (Hermitian case, the direction used in the paper):
if the Hermitian form associated with a Hermitian matrix `A` is positive definite on a complex
subspace `W` of `Fin d → ℂ`, then `finrank W` is at most the number of strictly positive
eigenvalues of `A`.  In other words, pulling back does not increase the positive index. -/
theorem sylvester_hermitian_finrank {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ (A *ᵥ x)).re) :
    Module.finrank ℂ W ≤ posIndex A := by
  classical
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set lam : Fin d → ℝ := hA.eigenvalues with hlam
  set P : Type := {i : Fin d // 0 < lam i} with hP
  have : Fintype P := Subtype.fintype _
  -- the map sending `x` to the coordinates of `x`, in the eigenbasis, at the positive eigenvalues
  let f : (Fin d → ℂ) →ₗ[ℂ] (P → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : P → Fin d)).comp (Matrix.mulVecLin (star U))
  have hinj : Function.Injective ⇑(f.comp W.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨z, hz⟩ hker
    have hzero : ∀ i : Fin d, 0 < lam i → ((star U) *ᵥ z) i = 0 := by
      intro i hi
      have := congrFun (LinearMap.mem_ker.mp hker) ⟨i, hi⟩
      simpa [f, LinearMap.funLeft] using this
    have hle : (star z ⬝ᵥ (A *ᵥ z)).re ≤ 0 := by
      rw [quadratic_form_eq_sum hA z]
      apply Finset.sum_nonpos
      intro i _
      rcases le_or_gt (hA.eigenvalues i) 0 with h | h
      · exact mul_nonpos_of_nonpos_of_nonneg h (Complex.normSq_nonneg _)
      · rw [show ((star U) *ᵥ z) i = 0 from hzero i h]
        simp
    have hz0 : z = 0 := by
      by_contra hne
      exact absurd hle (not_le.mpr (hW z hz hne))
    exact Subtype.ext hz0
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank ℂ (P → ℂ) = posIndex A := by
    rw [Module.finrank_pi, posIndex, dif_pos hA]
    exact (Nat.card_eq_fintype_card).symm
  simpa [h2] using h1

end Zeta23Redux.LinAlg

