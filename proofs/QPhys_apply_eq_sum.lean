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
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped InnerProductSpace

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of `H ψ` in an orthonormal eigenbasis of `H`. -/
lemma apply_eq_sum (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V) (mu : Fin n → ℝ)
    (hH : ∀ i, H (b i) = (mu i : ℂ) • b i) (psi : V) :
    H psi = ∑ i, ((mu i : ℂ) * ⟪b i, psi⟫_ℂ) • b i := by
  conv_lhs => rw [← b.sum_repr psi]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hH i, smul_smul, b.repr_apply_apply]
  ring_nf

/-- The `i`-th coefficient of `H ψ` is `μ i` times the `i`-th coefficient of `ψ`. -/
lemma inner_basis_apply (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V) (mu : Fin n → ℝ)
    (hH : ∀ i, H (b i) = (mu i : ℂ) • b i) (psi : V) (i : Fin n) :
    ⟪b i, H psi⟫_ℂ = (mu i : ℂ) * ⟪b i, psi⟫_ℂ := by
  rw [apply_eq_sum b H mu hH psi, inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right, b.inner_eq_one, mul_one]
  · intro j _ hj
    rw [inner_smul_right, b.inner_eq_zero hj.symm, mul_zero]
  · intro h; simp at h

/-- Parseval: `⟨ψ|ψ⟩ = ∑ᵢ |cᵢ|²` for the coefficients `cᵢ = ⟨bᵢ|ψ⟩`. -/
lemma inner_self_eq_sum (b : OrthonormalBasis (Fin n) ℂ V) (psi : V) :
    ⟪psi, psi⟫_ℂ = ((∑ i, ‖⟪b i, psi⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← b.sum_inner_mul_inner psi psi]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← inner_conj_symm (b i) psi]
  rw [show ⟪psi, b i⟫_ℂ * (starRingEnd ℂ) ⟪psi, b i⟫_ℂ
      = (1 : ℂ) * (⟪psi, b i⟫_ℂ * (starRingEnd ℂ) ⟪psi, b i⟫_ℂ) by ring,
    Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, norm_inner_symm]

/-- The expectation value `⟨ψ|H|ψ⟩` is the eigenvalue-weighted sum `∑ᵢ μᵢ |cᵢ|²`. -/
lemma inner_apply_eq_sum (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V) (mu : Fin n → ℝ)
    (hH : ∀ i, H (b i) = (mu i : ℂ) • b i) (psi : V) :
    ⟪psi, H psi⟫_ℂ = ((∑ i, mu i * ‖⟪b i, psi⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← b.sum_inner_mul_inner psi (H psi)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_basis_apply b H mu hH psi i, ← inner_conj_symm (b i) psi]
  rw [show ⟪psi, b i⟫_ℂ * ((mu i : ℂ) * (starRingEnd ℂ) ⟪psi, b i⟫_ℂ)
      = (mu i : ℂ) * (⟪psi, b i⟫_ℂ * (starRingEnd ℂ) ⟪psi, b i⟫_ℂ) by ring,
    Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, norm_inner_symm]

/-- **Variational bound.** If `H` has an orthonormal eigenbasis `b` with (real) eigenvalues `mu`,
and `E₀` is a lower bound for all the eigenvalues (the ground-state energy, i.e. the smallest
eigenvalue, being the sharp such bound), then for every nonzero state `ψ` the Rayleigh quotient
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E₀`. -/
theorem variational_bound (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V) (mu : Fin n → ℝ)
    (hH : ∀ i, H (b i) = (mu i : ℂ) • b i) (E0 : ℝ) (hE0 : ∀ i, E0 ≤ mu i)
    (psi : V) (hpsi : psi ≠ 0) :
    E0 ≤ (⟪psi, H psi⟫_ℂ).re / (⟪psi, psi⟫_ℂ).re := by
  have hden : (⟪psi, psi⟫_ℂ).re = ‖psi‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) psi
  have hpos : 0 < (⟪psi, psi⟫_ℂ).re := by
    rw [hden]
    have : 0 < ‖psi‖ := norm_pos_iff.mpr hpsi
    positivity
  rw [le_div_iff₀ hpos, inner_apply_eq_sum b H mu hH psi, inner_self_eq_sum b psi]
  simp only [Complex.ofReal_re]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hE0 i) (by positivity)

#print axioms QPhys.variational_bound

end QPhys

