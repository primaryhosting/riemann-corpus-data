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

/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QPhys

open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A (bounded, everywhere-defined) linear operator on a complex inner product space is
*symmetric* if it satisfies `⟪A u, v⟫ = ⟪u, A v⟫` for all vectors `u`, `v`. -/
def IsSymmetricOp (A : H →ₗ[ℂ] H) : Prop := ∀ u v : H, ⟪A u, v⟫_ℂ = ⟪u, A v⟫_ℂ

/-- The standard deviation (uncertainty) of the observable `A` in the state `ψ`:
the norm of `A ψ` after subtracting its mean value `⟪ψ, A ψ⟫`. -/
noncomputable def spread (A : H →ₗ[ℂ] H) (ψ : H) : ℝ := ‖A ψ - ⟪ψ, A ψ⟫_ℂ • ψ‖

lemma inner_centered {A B : H →ₗ[ℂ] H} {ψ : H} (hA : IsSymmetricOp A) (hψ : ‖ψ‖ = 1) :
    ⟪A ψ - ⟪ψ, A ψ⟫_ℂ • ψ, B ψ - ⟪ψ, B ψ⟫_ℂ • ψ⟫_ℂ
      = ⟪ψ, A (B ψ)⟫_ℂ - ⟪ψ, A ψ⟫_ℂ * ⟪ψ, B ψ⟫_ℂ := by
  have hself : ⟪ψ, ψ⟫_ℂ = 1 := by
    simp [inner_self_eq_norm_sq_to_K, hψ]
  have h1 : ⟪A ψ, B ψ⟫_ℂ = ⟪ψ, A (B ψ)⟫_ℂ := hA ψ (B ψ)
  have h2 : ⟪A ψ, ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := hA ψ ψ
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, h1, h2, hself]
  ring

/-- **Heisenberg uncertainty principle.**  Let `X` and `P` be symmetric operators
(position and momentum observables) on a complex inner product space, let `ψ` be a normalized
state, and assume the canonical commutation relation holds in the state `ψ`, i.e.
`⟪ψ, (X P - P X) ψ⟫ = i ℏ`.  Then the product of the uncertainties of `X` and `P` in the
state `ψ` is at least `ℏ / 2`. -/
theorem heisenberg_uncertainty {X P : H →ₗ[ℂ] H} {ψ : H} (hbar : ℝ)
    (hX : IsSymmetricOp X) (hP : IsSymmetricOp P) (hψ : ‖ψ‖ = 1)
    (hcomm : ⟪ψ, X (P ψ) - P (X ψ)⟫_ℂ = Complex.I * hbar) :
    spread X ψ * spread P ψ ≥ hbar / 2 := by
  set u : H := X ψ - ⟪ψ, X ψ⟫_ℂ • ψ with hu
  set v : H := P ψ - ⟪ψ, P ψ⟫_ℂ • ψ with hv
  have huv : ⟪u, v⟫_ℂ = ⟪ψ, X (P ψ)⟫_ℂ - ⟪ψ, X ψ⟫_ℂ * ⟪ψ, P ψ⟫_ℂ := inner_centered hX hψ
  have hvu : ⟪v, u⟫_ℂ = ⟪ψ, P (X ψ)⟫_ℂ - ⟪ψ, P ψ⟫_ℂ * ⟪ψ, X ψ⟫_ℂ := inner_centered hP hψ
  have hconj : ⟪v, u⟫_ℂ = conj ⟪u, v⟫_ℂ := (inner_conj_symm v u).symm
  have hdiff : ⟪u, v⟫_ℂ - conj ⟪u, v⟫_ℂ = Complex.I * hbar := by
    rw [← hconj, huv, hvu, ← hcomm, inner_sub_right]
    ring
  have him2 : (⟪v, u⟫_ℂ).im = -(⟪u, v⟫_ℂ).im := by
    rw [hconj, Complex.conj_im]
  have him : (⟪u, v⟫_ℂ).im = hbar / 2 := by
    have := congrArg Complex.im hdiff
    simp [Complex.sub_im, Complex.mul_im] at this
    linarith
  have h1 : |hbar / 2| ≤ ‖⟪u, v⟫_ℂ‖ := by
    rw [← him]
    exact Complex.abs_im_le_norm _
  have h2 : ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have : hbar / 2 ≤ |hbar / 2| := le_abs_self _
  simp only [spread, ← hu, ← hv, ge_iff_le]
  linarith

/-- `IsSymmetricOp` is exactly Mathlib's `LinearMap.IsSymmetric`. -/
lemma isSymmetricOp_iff_isSymmetric (A : H →ₗ[ℂ] H) : IsSymmetricOp A ↔ A.IsSymmetric := Iff.rfl

/-- The expectation value of a symmetric observable in any state is real. -/
lemma mean_isReal {A : H →ₗ[ℂ] H} (hA : IsSymmetricOp A) (ψ : H) :
    (⟪ψ, A ψ⟫_ℂ).im = 0 := by
  have h : conj ⟪ψ, A ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := by
    rw [inner_conj_symm]
    exact hA ψ ψ
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- **Heisenberg uncertainty from the canonical commutation relation.**
If the operator identity `X P - P X = i ℏ` holds (on all vectors), then every normalized state
satisfies `Δx · Δp ≥ ℏ / 2`. -/
theorem heisenberg_uncertainty_of_ccr {X P : H →ₗ[ℂ] H} (hbar : ℝ)
    (hX : IsSymmetricOp X) (hP : IsSymmetricOp P)
    (hccr : ∀ φ : H, X (P φ) - P (X φ) = (Complex.I * hbar) • φ)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    spread X ψ * spread P ψ ≥ hbar / 2 := by
  refine heisenberg_uncertainty hbar hX hP hψ ?_
  have hself : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  rw [hccr ψ, inner_smul_right, hself, mul_one]

/-- The squared (variance) form of the uncertainty principle: `(Δx)² (Δp)² ≥ ℏ² / 4`. -/
theorem heisenberg_uncertainty_sq {X P : H →ₗ[ℂ] H} {ψ : H} (hbar : ℝ)
    (hX : IsSymmetricOp X) (hP : IsSymmetricOp P) (hψ : ‖ψ‖ = 1)
    (hcomm : ⟪ψ, X (P ψ) - P (X ψ)⟫_ℂ = Complex.I * hbar) :
    spread X ψ ^ 2 * spread P ψ ^ 2 ≥ hbar ^ 2 / 4 := by
  have h1 : spread X ψ * spread P ψ ≥ hbar / 2 := heisenberg_uncertainty hbar hX hP hψ hcomm
  have h2 : spread X ψ * spread P ψ ≥ -hbar / 2 := by
    have hswap : spread P ψ * spread X ψ ≥ -hbar / 2 := by
      refine heisenberg_uncertainty (-hbar) hP hX hψ ?_
      have h3 : ⟪ψ, P (X ψ) - X (P ψ)⟫_ℂ = -⟪ψ, X (P ψ) - P (X ψ)⟫_ℂ := by
        rw [← inner_neg_right]
        congr 1
        abel
      rw [h3, hcomm]
      push_cast
      ring
    rwa [mul_comm] at hswap
  have h5 : (hbar / 2) ^ 2 ≤ (spread X ψ * spread P ψ) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  calc hbar ^ 2 / 4 = (hbar / 2) ^ 2 := by ring
    _ ≤ (spread X ψ * spread P ψ) ^ 2 := h5
    _ = spread X ψ ^ 2 * spread P ψ ^ 2 := by ring


/-!
### Non-vacuity

The hypotheses of `QPhys.heisenberg_uncertainty` are satisfiable: the Pauli matrices `σx`, `σy`
acting on `ℂ²` are symmetric, and in the state `e₀` they satisfy `⟪ψ, (σx σy - σy σx) ψ⟫ = 2 i`.
-/

namespace Example

/-- The Pauli matrix `σx`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `σy`. -/
noncomputable def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- `σx` as an operator on `ℂ²`. -/
noncomputable def opX : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin pauliX

/-- `σy` as an operator on `ℂ²`. -/
noncomputable def opP : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin pauliY

/-- The normalized state `e₀ ∈ ℂ²`. -/
noncomputable def state : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

lemma pauliX_isHermitian : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose]

lemma pauliY_isHermitian : pauliY.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.conjTranspose]

lemma opX_symm : IsSymmetricOp opX := Matrix.isHermitian_iff_isSymmetric.mp pauliX_isHermitian

lemma opP_symm : IsSymmetricOp opP := Matrix.isHermitian_iff_isSymmetric.mp pauliY_isHermitian

lemma state_norm : ‖state‖ = 1 := by simp [state]

lemma commutator_state :
    ⟪state, opX (opP state) - opP (opX state)⟫_ℂ = Complex.I * ((2 : ℝ) : ℂ) := by
  simp only [opX, opP, state, Matrix.toLpLin_apply, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_two, PiLp.sub_apply, EuclideanSpace.single_apply, Matrix.mulVec, dotProduct,
    pauliX, pauliY]
  norm_num [Complex.ext_iff]

/-- The hypotheses of the uncertainty principle are non-vacuous. -/
theorem hypotheses_satisfiable :
    ∃ (X P : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
      (ψ : EuclideanSpace ℂ (Fin 2)) (hbar : ℝ),
      0 < hbar ∧ IsSymmetricOp X ∧ IsSymmetricOp P ∧ ‖ψ‖ = 1 ∧
        ⟪ψ, X (P ψ) - P (X ψ)⟫_ℂ = Complex.I * hbar :=
  ⟨opX, opP, state, 2, by norm_num, opX_symm, opP_symm, state_norm, commutator_state⟩

end Example


end QPhys

