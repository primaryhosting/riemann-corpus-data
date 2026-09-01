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

open scoped InnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An operator `A` on a complex inner product space is *symmetric* (an observable) if
`⟪A x, y⟫ = ⟪x, A y⟫` for all `x y`. -/
def IsSymmetricOp (A : H →ₗ[ℂ] H) : Prop := ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/
noncomputable def expect (A : H →ₗ[ℂ] H) (ψ : H) : ℂ := ⟪ψ, A ψ⟫_ℂ

/-- The standard deviation (uncertainty) `ΔA = ‖(A - ⟨A⟩) ψ‖` of an observable `A`
in the state `ψ`. -/
noncomputable def spread (A : H →ₗ[ℂ] H) (ψ : H) : ℝ := ‖A ψ - expect A ψ • ψ‖

/-- The expectation value of a symmetric operator is real. -/
lemma conj_expect (A : H →ₗ[ℂ] H) (hA : IsSymmetricOp A) (ψ : H) :
    (starRingEnd ℂ) (expect A ψ) = expect A ψ := by
  rw [expect, inner_conj_symm, hA]

/-- Expanding the inner product of the two centered vectors. -/
lemma inner_centered (A B : H →ₗ[ℂ] H) (hA : IsSymmetricOp A) (ψ : H)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) :
    ⟪A ψ - expect A ψ • ψ, B ψ - expect B ψ • ψ⟫_ℂ
      = ⟪ψ, A (B ψ)⟫_ℂ - expect A ψ * expect B ψ := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, hA, hA, hψ, conj_expect A hA]
  simp only [expect]
  ring

/-- **The Robertson uncertainty relation.**  For any two symmetric operators `A`, `B`
(observables) on a complex inner product space and any normalized state `ψ`,
`ΔA · ΔB ≥ ‖⟪ψ, [A, B] ψ⟫‖ / 2`, where `[A, B] = A B - B A` is the commutator.

The proof is the classical one: expand the inner product of the centered vectors
`f = (A - ⟨A⟩)ψ`, `g = (B - ⟨B⟩)ψ`, note that `⟪f, g⟫ - ⟪g, f⟫ = ⟪ψ, [A,B] ψ⟫` equals
`2 i Im ⟪f, g⟫`, and apply the Cauchy–Schwarz inequality
`norm_inner_le_norm : ‖⟪f, g⟫‖ ≤ ‖f‖ * ‖g‖` from Mathlib. -/
theorem robertson_uncertainty (A B : H →ₗ[ℂ] H)
    (hA : IsSymmetricOp A) (hB : IsSymmetricOp B)
    (ψ : H) (hψ : ‖ψ‖ = 1) :
    spread A ψ * spread B ψ ≥ ‖⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ‖ / 2 := by
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  set f := A ψ - expect A ψ • ψ with hf
  set g := B ψ - expect B ψ • ψ with hg
  -- the commutator identity transported to the centered vectors
  have hkey : ⟪f, g⟫_ℂ - ⟪g, f⟫_ℂ = ⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ := by
    rw [hf, hg, inner_centered A B hA ψ hψψ, inner_centered B A hB ψ hψψ, inner_sub_right]
    ring
  -- the commutator expectation is `2 i Im ⟪f, g⟫`
  have hconj : ⟪g, f⟫_ℂ = (starRingEnd ℂ) ⟪f, g⟫_ℂ := (inner_conj_symm g f).symm
  have hnorm : ‖⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ‖ = 2 * |(⟪f, g⟫_ℂ).im| := by
    rw [← hkey, hconj, Complex.sub_conj]
    simp
  rw [hnorm]
  have hcs : ‖⟪f, g⟫_ℂ‖ ≤ ‖f‖ * ‖g‖ := norm_inner_le_norm f g
  have him : |(⟪f, g⟫_ℂ).im| ≤ ‖⟪f, g⟫_ℂ‖ := Complex.abs_im_le_norm _
  have : ‖f‖ * ‖g‖ = spread A ψ * spread B ψ := rfl
  linarith [him.trans hcs]

/-- **Heisenberg's uncertainty principle.**  If `A` and `B` are symmetric operators
(observables, e.g. position and momentum) on a complex inner product space satisfying the
canonical commutation relation `[A, B] = i ℏ`, then for every normalized state `ψ`
the product of the uncertainties satisfies `ΔA · ΔB ≥ ℏ / 2`. -/
theorem heisenberg_uncertainty (A B : H →ₗ[ℂ] H)
    (hA : IsSymmetricOp A) (hB : IsSymmetricOp B)
    (hbar : ℝ)
    (hcomm : ∀ x : H, A (B x) - B (A x) = (Complex.I * hbar) • x)
    (ψ : H) (hψ : ‖ψ‖ = 1) :
    spread A ψ * spread B ψ ≥ hbar / 2 := by
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hcomm' : ⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ = Complex.I * hbar := by
    rw [hcomm ψ, inner_smul_right, hψψ, mul_one]
  have h := robertson_uncertainty A B hA hB ψ hψ
  rw [hcomm'] at h
  have : ‖Complex.I * (hbar : ℂ)‖ = |hbar| := by simp
  rw [this] at h
  have : hbar ≤ |hbar| := le_abs_self _
  linarith

/-! ### A concrete instance: the Pauli observables on a qubit

This section checks that the hypotheses of `robertson_uncertainty` are satisfiable with a
*nonzero* commutator, so that the uncertainty bound above is not vacuous. -/

/-- The Pauli observable `σₓ` acting on a qubit. -/
noncomputable def sigmaX : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, 1; 1, 0]

/-- The Pauli observable `σ_y` acting on a qubit. -/
noncomputable def sigmaY : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, -Complex.I; Complex.I, 0]

/-- The normalized state `|0⟩`. -/
noncomputable def qubitZero : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

lemma isSymmetricOp_sigmaX : IsSymmetricOp sigmaX := by
  have h : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
    simp [Matrix.IsHermitian, ← Matrix.ext_iff, Fin.forall_fin_two]
  exact Matrix.isHermitian_iff_isSymmetric.mp h

lemma isSymmetricOp_sigmaY : IsSymmetricOp sigmaY := by
  have h : (!![0, -Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
    simp [Matrix.IsHermitian, ← Matrix.ext_iff, Fin.forall_fin_two]
  exact Matrix.isHermitian_iff_isSymmetric.mp h

lemma norm_qubitZero : ‖qubitZero‖ = 1 := by
  simp [qubitZero]

lemma inner_qubitZero_commutator :
    ⟪qubitZero, sigmaX (sigmaY qubitZero) - sigmaY (sigmaX qubitZero)⟫_ℂ = 2 * Complex.I := by
  simp [sigmaX, sigmaY, qubitZero, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.vecHead, Matrix.vecTail, Matrix.col]
  ring

/-- Non-vacuity check: for the qubit observables `σₓ`, `σ_y` in the state `|0⟩` the
Robertson bound gives the nontrivial inequality `Δσₓ · Δσ_y ≥ 1`. -/
theorem qubit_uncertainty : spread sigmaX qubitZero * spread sigmaY qubitZero ≥ 1 := by
  have h := robertson_uncertainty sigmaX sigmaY isSymmetricOp_sigmaX isSymmetricOp_sigmaY
    qubitZero norm_qubitZero
  rw [inner_qubitZero_commutator] at h
  have h2 : ‖(2 : ℂ) * Complex.I‖ = 2 := by simp
  rw [h2] at h
  linarith

end QPhys

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

