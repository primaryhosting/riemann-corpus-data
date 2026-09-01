/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

section

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of `H ψ` in an eigenbasis `b` of `H` with eigenvalues `E`. -/
lemma apply_eq_sum_eigen (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (E : ι → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) :
    H ψ = ∑ i, ((E i : ℂ) * ⟪b i, ψ⟫_ℂ) • b i := by
  conv_lhs => rw [← b.sum_repr' ψ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hH i, smul_smul, mul_comm]

/-- The expectation value `⟨ψ|H|ψ⟩` is the eigenvalue-weighted sum of the squared
moduli of the expansion coefficients of `ψ` in the eigenbasis. -/
lemma re_inner_apply_eq_sum (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (E : ι → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) :
    (⟪ψ, H ψ⟫_ℂ).re = ∑ i, E i * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 := by
  rw [apply_eq_sum_eigen b H E hH ψ, inner_sum]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, ← inner_conj_symm (b i) ψ]
  rw [mul_assoc, Complex.conj_mul', Complex.norm_conj]
  norm_cast

/-- **Variational bound (unnormalised form).** If `H` has an orthonormal eigenbasis with all
eigenvalues bounded below by `E₀`, then `E₀ ‖ψ‖² ≤ ⟨ψ|H|ψ⟩` for every state `ψ`. -/
theorem variational_bound_mul_normSq (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (E : ι → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (E₀ : ℝ) (hE₀ : ∀ i, E₀ ≤ E i) (ψ : V) :
    E₀ * ‖ψ‖ ^ 2 ≤ (⟪ψ, H ψ⟫_ℂ).re := by
  rw [re_inner_apply_eq_sum b H E hH ψ, ← b.sum_sq_norm_inner_right ψ, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hE₀ i) (by positivity)

/-- **The ground-state variational bound.**
Let `H` be a (linear) Hamiltonian on a complex inner product space possessing an orthonormal
eigenbasis `b` with real eigenvalues `E i`, and let `E₀` be a lower bound for the spectrum
(e.g. the ground-state energy). Then for every nonzero state `ψ`,
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E₀`. -/
theorem variational_bound (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (E : ι → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (E₀ : ℝ) (hE₀ : ∀ i, E₀ ≤ E i)
    (ψ : V) (hψ : ψ ≠ 0) :
    E₀ ≤ (⟪ψ, H ψ⟫_ℂ).re / (⟪ψ, ψ⟫_ℂ).re := by
  have hnorm : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have hpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by
    have : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
    positivity
  rw [hnorm, le_div_iff₀ hpos]
  exact variational_bound_mul_normSq b H E hH E₀ hE₀ ψ

end

section Symmetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- **Variational bound for a symmetric (self-adjoint) Hamiltonian.**
On a finite-dimensional complex Hilbert space, if `H` is symmetric and `E₀` is a lower bound
for all of its (necessarily real) eigenvalues — e.g. `E₀` is the ground-state energy — then
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E₀` for every nonzero state `ψ`.
The orthonormal eigenbasis is supplied by the finite-dimensional spectral theorem. -/
theorem variational_bound_isSymmetric {H : V →ₗ[ℂ] V} (hsymm : H.IsSymmetric) (E₀ : ℝ)
    (hE₀ : ∀ μ : ℝ, Module.End.HasEigenvalue H (μ : ℂ) → E₀ ≤ μ) (ψ : V) (hψ : ψ ≠ 0) :
    E₀ ≤ (⟪ψ, H ψ⟫_ℂ).re / (⟪ψ, ψ⟫_ℂ).re :=
  variational_bound (hsymm.eigenvectorBasis (n := Module.finrank ℂ V) rfl) H
    (hsymm.eigenvalues rfl) (fun i => hsymm.apply_eigenvectorBasis rfl i) E₀
    (fun i => hE₀ _ (hsymm.hasEigenvalue_eigenvalues rfl i)) ψ hψ

end Symmetric

end QPhys

