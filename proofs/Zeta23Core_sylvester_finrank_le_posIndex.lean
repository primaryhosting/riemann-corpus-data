/-
# Sylvester Finrank Le Pos Index
Category: Brockian Corpus
Target: Zeta23Core.sylvester_finrank_le_posIndex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Core

open Matrix Unitary

/-- The number of positive eigenvalues of a Hermitian matrix `A`, i.e. `n₊(A)`. -/
noncomputable def posIndex {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : n // 0 < hA.eigenvalues i}

/-- If `A = U * diagonal d * Uᴴ` with `d` real-valued, then the real quadratic form of `A`
is the weighted sum of squares `∑ i, d i * ‖(Uᴴ x) i‖ ^ 2`. -/
theorem re_quadraticForm_eq_sum_of_spectral_decomposition {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    [Fintype n] [DecidableEq n] (A U : Matrix n n 𝕜) (d : n → ℝ)
    (hspec : A = U * diagonal (RCLike.ofReal ∘ d) * star U) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) = ∑ i, d i * ‖(star U *ᵥ x) i‖ ^ 2 := by
  have h1 : star x ⬝ᵥ (A *ᵥ x)
      = star (star U *ᵥ x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ d) *ᵥ (star U *ᵥ x)) := by
    rw [hspec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
      ← Matrix.star_eq_conjTranspose, star_star]
  rw [h1, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  simp only [Pi.star_apply, Function.comp_apply, ← mul_assoc, RCLike.star_def]
  rw [mul_comm (starRingEnd 𝕜 _), mul_assoc, RCLike.conj_mul]
  simp

/-- **Sylvester's law of inertia**, hard direction: if the Hermitian form associated with a
Hermitian matrix `A` is positive definite on a subspace `W` of `n → 𝕜`, then
`finrank 𝕜 W ≤ posIndex hA`, the number of positive eigenvalues of `A`. -/
theorem sylvester_finrank_le_posIndex {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) (W : Submodule 𝕜 (n → 𝕜))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x))) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary with hU
  have hspec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply]
  -- The map sending `x ∈ W` to the coordinates of `Uᴴ x` at the positive eigenvalues.
  set f : W →ₗ[𝕜] ({i : n // 0 < hA.eigenvalues i} → 𝕜) :=
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i : n // 0 < hA.eigenvalues i} → n)).comp
      ((star U).mulVecLin.comp W.subtype) with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro x hx
    simp only [LinearMap.mem_ker, hf, LinearMap.comp_apply, Matrix.mulVecLin_apply,
      Submodule.subtype_apply] at hx
    have hzero : ∀ i : n, 0 < hA.eigenvalues i → (star U *ᵥ (x : n → 𝕜)) i = 0 := by
      intro i hi
      have := congrFun hx ⟨i, hi⟩
      simpa using this
    by_contra hne
    have hx0 : (x : n → 𝕜) ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos := hW x x.2 hx0
    rw [re_quadraticForm_eq_sum_of_spectral_decomposition A U hA.eigenvalues hspec] at hpos
    have hle : ∑ i, hA.eigenvalues i * ‖(star U *ᵥ (x : n → 𝕜)) i‖ ^ 2 ≤ 0 := by
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hA.eigenvalues i) with h | h
      · rw [hzero i h]; simp
      · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card] at hle

end Zeta23Core

