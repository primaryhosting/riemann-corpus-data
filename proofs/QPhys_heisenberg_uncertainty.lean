/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Heisenberg uncertainty principle.**

For two self-adjoint (symmetric) operators `A`, `B` on a complex inner product space and a
normalized state `psi` satisfying the canonical commutation relation
`A (B psi) - B (A psi) = (i * ℏ) • psi`, the standard deviations
`Δ A = ‖A psi - ⟪psi, A psi⟫ • psi‖` and `Δ B = ‖B psi - ⟪psi, B psi⟫ • psi‖`
satisfy `Δ A * Δ B ≥ ℏ / 2`.

(Here `⟪psi, A psi⟫` is the expectation value of `A` in the state `psi`; it is automatically real.)
The proof is the classical one: the commutator identity forces the imaginary part of
`⟪A psi - ⟪A⟫ psi, B psi - ⟪B⟫ psi⟫` to be `ℏ / 2`, and Cauchy–Schwarz
(`norm_inner_le_norm`) bounds it by the product of the norms. -/
theorem heisenberg_uncertainty
    (A B : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hB : ∀ x y : H, ⟪B x, y⟫_ℂ = ⟪x, B y⟫_ℂ)
    (psi : H) (hpsi : ‖psi‖ = 1) (hbar : ℝ)
    (hcomm : A (B psi) - B (A psi) = (Complex.I * hbar) • psi) :
    hbar / 2 ≤ ‖A psi - ⟪psi, A psi⟫_ℂ • psi‖ * ‖B psi - ⟪psi, B psi⟫_ℂ • psi‖ := by
  set a : ℂ := ⟪psi, A psi⟫_ℂ with ha_def
  set b : ℂ := ⟪psi, B psi⟫_ℂ with hb_def
  set u : H := A psi - a • psi with hu_def
  set v : H := B psi - b • psi with hv_def
  have hself : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  have hA' : ⟪A psi, psi⟫_ℂ = a := by rw [hA]
  have hB' : ⟪B psi, psi⟫_ℂ = b := by rw [hB]
  have haconj : conj a = a := by
    rw [ha_def, ← inner_conj_symm, ← ha_def] at hA'
    exact hA'
  have hbconj : conj b = b := by
    rw [hb_def, ← inner_conj_symm, ← hb_def] at hB'
    exact hB'
  -- The antisymmetric part of `⟪u, v⟫` computes the commutator.
  have hcross : ⟪A psi, B psi⟫_ℂ - ⟪B psi, A psi⟫_ℂ = Complex.I * hbar := by
    have h1 : ⟪A psi, B psi⟫_ℂ = ⟪psi, A (B psi)⟫_ℂ := by rw [hA]
    have h2 : ⟪B psi, A psi⟫_ℂ = ⟪psi, B (A psi)⟫_ℂ := by rw [hB]
    rw [h1, h2, ← inner_sub_right, hcomm, inner_smul_right, hself, mul_one]
  have hinner : ⟪u, v⟫_ℂ = ⟪A psi, B psi⟫_ℂ - a * b := by
    simp only [hu_def, hv_def, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, hself, hA', haconj]
    ring
  have hinner' : ⟪v, u⟫_ℂ = ⟪B psi, A psi⟫_ℂ - a * b := by
    simp only [hu_def, hv_def, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, hself, hB', hbconj]
    ring
  have hdiff : ⟪u, v⟫_ℂ - conj ⟪u, v⟫_ℂ = Complex.I * hbar := by
    rw [inner_conj_symm, hinner, hinner']
    rw [show ⟪A psi, B psi⟫_ℂ - a * b - (⟪B psi, A psi⟫_ℂ - a * b)
        = ⟪A psi, B psi⟫_ℂ - ⟪B psi, A psi⟫_ℂ by ring, hcross]
  have him : (⟪u, v⟫_ℂ).im = hbar / 2 := by
    have := congrArg Complex.im hdiff
    simp [Complex.sub_im, Complex.mul_im] at this
    have hvu : (⟪v, u⟫_ℂ).im = -(⟪u, v⟫_ℂ).im := by
      rw [← inner_conj_symm v u, Complex.conj_im]
    linarith
  calc hbar / 2 ≤ |(⟪u, v⟫_ℂ).im| := by rw [him]; exact le_abs_self _
    _ ≤ ‖⟪u, v⟫_ℂ‖ := Complex.abs_im_le_norm _
    _ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm _ _

end QPhys

