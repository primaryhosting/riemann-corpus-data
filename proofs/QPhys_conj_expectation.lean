/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace
open Matrix

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

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The spread (standard deviation) of the observable `A` in the state `psi`:
the norm of `A psi` after subtracting its mean value `⟪psi, A psi⟫ • psi`. -/
noncomputable def spread (A : H →ₗ[ℂ] H) (psi : H) : ℝ :=
  ‖A psi - (⟪psi, A psi⟫_ℂ) • psi‖

/-- `A` is symmetric (formally self-adjoint) if `⟪A u, v⟫ = ⟪u, A v⟫`. -/
def IsSymmetricOp (A : H →ₗ[ℂ] H) : Prop := ∀ u v : H, ⟪A u, v⟫_ℂ = ⟪u, A v⟫_ℂ

/-- For a symmetric operator, the expectation value `⟪psi, A psi⟫` is real. -/
lemma conj_expectation {A : H →ₗ[ℂ] H} (hA : IsSymmetricOp A) (psi : H) :
    (starRingEnd ℂ) (⟪psi, A psi⟫_ℂ) = ⟪psi, A psi⟫_ℂ := by
  rw [inner_conj_symm, hA]

/-- For a symmetric operator `A` and a normalized state, the square of the spread is the
usual variance `⟨A²⟩ - ⟨A⟩²`. -/
lemma spread_sq_eq {A : H →ₗ[ℂ] H} (hA : IsSymmetricOp A) {psi : H} (hpsi : ‖psi‖ = 1) :
    (spread A psi) ^ 2 = (⟪psi, A (A psi)⟫_ℂ).re - ((⟪psi, A psi⟫_ℂ).re) ^ 2 := by
  have hself : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  set a : ℂ := ⟪psi, A psi⟫_ℂ with ha_def
  have hac : (starRingEnd ℂ) a = a := conj_expectation hA psi
  have haim : a.im = 0 := by
    have := congrArg Complex.im hac
    rw [Complex.conj_im] at this
    linarith
  have hAp : ⟪A psi, psi⟫_ℂ = a := by rw [ha_def, hA]
  have hnorm : (spread A psi) ^ 2 = (⟪A psi - a • psi, A psi - a • psi⟫_ℂ).re := by
    rw [spread, ← ha_def, ← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
  rw [hnorm]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hself,
    hac, hAp, mul_one, ← hA psi (A psi)]
  simp only [Complex.sub_re, Complex.mul_re, haim, ← ha_def]
  ring

/-- **Heisenberg uncertainty principle** (absolute-value form).

For symmetric operators `X` and `P` on a complex inner product space and a normalized state
`psi` satisfying the canonical commutation relation `[X, P] psi = i·ℏ·psi`, the product of the
spreads of `X` and `P` in the state `psi` is at least `|ℏ|/2`. -/
theorem heisenberg_uncertainty_abs
    {X P : H →ₗ[ℂ] H} (hX : IsSymmetricOp X) (hP : IsSymmetricOp P)
    {hbar : ℝ} {psi : H} (hpsi : ‖psi‖ = 1)
    (hcomm : X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi) :
    |hbar| / 2 ≤ spread X psi * spread P psi := by
  set a : ℂ := ⟪psi, X psi⟫_ℂ with ha_def
  set b : ℂ := ⟪psi, P psi⟫_ℂ with hb_def
  have hself : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  have hac : (starRingEnd ℂ) a = a := conj_expectation hX psi
  have hbc : (starRingEnd ℂ) b = b := conj_expectation hP psi
  set u : H := X psi - a • psi with hu
  set v : H := P psi - b • psi with hv
  -- the commutator gives the imaginary part of ⟪u, v⟫
  have hcm : ⟪X psi, P psi⟫_ℂ - ⟪P psi, X psi⟫_ℂ = Complex.I * hbar := by
    have h := congrArg (fun w => ⟪psi, w⟫_ℂ) hcomm
    simp only [inner_sub_right, inner_smul_right, hself, mul_one] at h
    rw [hX psi (P psi), hP psi (X psi)]
    exact h
  have huv : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * hbar := by
    have hXp : ⟪X psi, psi⟫_ℂ = a := by rw [ha_def, hX]
    have hPp : ⟪P psi, psi⟫_ℂ = b := by rw [hb_def, hP]
    simp only [hu, hv, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hself, hac, hbc, mul_one, hXp, hPp, ← ha_def, ← hb_def]
    rw [← hcm]; ring
  have hconj : ⟪v, u⟫_ℂ = (starRingEnd ℂ) (⟪u, v⟫_ℂ) := (inner_conj_symm v u).symm
  have him : (⟪u, v⟫_ℂ).im = hbar / 2 := by
    rw [hconj] at huv
    have h2 := congrArg Complex.im huv
    rw [Complex.sub_im, Complex.conj_im] at h2
    simp [Complex.mul_im] at h2
    linarith
  -- Cauchy-Schwarz
  calc |hbar| / 2 = |(⟪u, v⟫_ℂ).im| := by rw [him, abs_div]; norm_num
    _ ≤ ‖⟪u, v⟫_ℂ‖ := Complex.abs_im_le_norm _
    _ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm _ _
    _ = spread X psi * spread P psi := rfl

/-- **Heisenberg uncertainty principle**: `Δx · Δp ≥ ℏ / 2`.

For symmetric (formally self-adjoint) position and momentum operators `X`, `P` on a complex
inner product space and a normalized state `psi` obeying the canonical commutation relation
`[X, P] psi = i·ℏ·psi`, the product of the standard deviations of `X` and `P` in the state
`psi` is at least `ℏ / 2`. The proof combines the commutator identity with the
Cauchy–Schwarz inequality (`norm_inner_le_norm` in Mathlib). -/
theorem heisenberg_uncertainty
    {X P : H →ₗ[ℂ] H} (hX : IsSymmetricOp X) (hP : IsSymmetricOp P)
    {hbar : ℝ} {psi : H} (hpsi : ‖psi‖ = 1)
    (hcomm : X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi) :
    spread X psi * spread P psi ≥ hbar / 2 :=
  le_trans (by linarith [le_abs_self hbar]) (heisenberg_uncertainty_abs hX hP hpsi hcomm)

/-! ### The hypotheses are satisfiable and the bound is sharp

On `ℂ²` the Pauli matrices `σₓ`, `σ_y` are symmetric and satisfy `[σₓ, σ_y] e₀ = 2i e₀`,
with both spreads equal to `1`, so equality holds in the uncertainty relation with `ℏ = 2`. -/

/-- The Pauli `σₓ` matrix as an operator on `ℂ²`, playing the role of the position observable. -/
noncomputable def pauliXOp : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, 1; 1, 0]

/-- The Pauli `σ_y` matrix as an operator on `ℂ²`, playing the role of the momentum observable. -/
noncomputable def pauliYOp : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, -Complex.I; Complex.I, 0]

/-- The normalized state `e₀ = (1, 0)` of `ℂ²`. -/
def state0 : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]

/-- The hypotheses of `QPhys.heisenberg_uncertainty` are satisfiable with `ℏ ≠ 0`, and the
bound `Δx·Δp ≥ ℏ/2` is sharp: for the Pauli operators on `ℂ²` and the state `e₀`, equality holds
with `ℏ = 2`. -/
theorem heisenberg_uncertainty_sharp :
    ∃ (X P : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
      (psi : EuclideanSpace ℂ (Fin 2)) (hbar : ℝ),
      0 < hbar ∧ IsSymmetricOp X ∧ IsSymmetricOp P ∧ ‖psi‖ = 1 ∧
        X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi ∧
        spread X psi * spread P psi = hbar / 2 := by
  refine ⟨pauliXOp, pauliYOp, state0, 2, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    simp [pauliXOp, PiLp.inner_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      RCLike.inner_apply]
    ring
  · intro u v
    simp [pauliYOp, PiLp.inner_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      RCLike.inner_apply]
    ring
  · simp [state0, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  · ext i
    fin_cases i
    · simp [pauliXOp, pauliYOp, state0, dotProduct, Fin.sum_univ_two]
      ring
    · simp [pauliXOp, pauliYOp, state0, dotProduct, Fin.sum_univ_two]
  · have hX0 : ⟪state0, pauliXOp state0⟫_ℂ = 0 := by
      simp [pauliXOp, state0, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
    have hP0 : ⟪state0, pauliYOp state0⟫_ℂ = 0 := by
      simp [pauliYOp, state0, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
    have hXs : spread pauliXOp state0 = 1 := by
      rw [spread, hX0]
      simp [pauliXOp, state0, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    have hPs : spread pauliYOp state0 = 1 := by
      rw [spread, hP0]
      simp [pauliYOp, state0, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [hXs, hPs]
    norm_num

end QPhys

