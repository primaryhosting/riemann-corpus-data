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

open scoped ComplexConjugate

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Action of the Hamiltonian on a basis vector, tested against `ψ`:
if `H` has orthonormal eigenbasis `b` with (real) eigenvalues `E`, then
`⟪bᵢ, Hψ⟫ = Eᵢ ⟪bᵢ, ψ⟫`. -/
lemma inner_basis_apply (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V)
    (E : Fin n → ℝ) (hE : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) (i : Fin n) :
    inner ℂ (b i) (H ψ) = (E i : ℂ) * inner ℂ (b i) ψ := by
  conv_lhs => rw [← b.sum_repr' ψ]
  rw [map_sum]
  simp only [map_smul, hE, smul_smul, inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single i]
  · rw [orthonormal_iff_ite.mp b.orthonormal]
    simp [mul_comm]
  · intro j _ hj
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp [Ne.symm hj]
  · intro h; simp at h

/-- Expansion of the expectation value in the eigenbasis. -/
lemma inner_self_expansion (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V)
    (E : Fin n → ℝ) (hE : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) :
    inner ℂ ψ (H ψ) = ∑ i, ((E i * ‖inner ℂ (b i) ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← b.sum_inner_mul_inner ψ (H ψ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_basis_apply b H E hE ψ i, ← inner_conj_symm (b i) ψ]
  push_cast
  rw [RCLike.norm_conj, mul_comm (inner ℂ ψ (b i)), mul_assoc,
    mul_comm ((starRingEnd ℂ) (inner ℂ ψ (b i))), Complex.mul_conj']

/-- Norm squared expanded in the eigenbasis. -/
lemma norm_sq_expansion (b : OrthonormalBasis (Fin n) ℂ V) (ψ : V) :
    ‖ψ‖ ^ 2 = ∑ i, ‖inner ℂ (b i) ψ‖ ^ 2 := by
  rw [← b.repr.norm_map ψ, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [b.repr_apply_apply]

/-- **Variational bound (Rayleigh–Ritz), normalized form.**
Same as `QPhys.variational_bound`, with the denominator written as `‖ψ‖ ^ 2`. -/
theorem variational_bound_norm_sq (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V)
    (E : Fin n → ℝ) (hE : ∀ i, H (b i) = (E i : ℂ) • b i)
    (E₀ : ℝ) (hE₀ : ∀ i, E₀ ≤ E i)
    (ψ : V) (hψ : ψ ≠ 0) :
    E₀ ≤ (inner ℂ ψ (H ψ) : ℂ).re / ‖ψ‖ ^ 2 := by
  have hpos : (0:ℝ) < ‖ψ‖ ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have hre : (inner ℂ ψ (H ψ) : ℂ).re = ∑ i, E i * ‖inner ℂ (b i) ψ‖ ^ 2 := by
    rw [inner_self_expansion b H E hE ψ]
    rw [Complex.re_sum]
    simp [-Complex.ofReal_pow]
  rw [hre, norm_sq_expansion b ψ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hE₀ i) (by positivity)

/-- **Variational bound (Rayleigh–Ritz).**
Let `H` be a Hamiltonian on a finite-dimensional complex inner product space with an
orthonormal eigenbasis `b` and real eigenvalues `E`, and let `E₀` be a lower bound for all
the eigenvalues (the ground-state energy). Then for every nonzero state `ψ` the Rayleigh
quotient satisfies `⟪ψ, Hψ⟫ / ⟪ψ, ψ⟫ ≥ E₀`. -/
theorem variational_bound (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V)
    (E : Fin n → ℝ) (hE : ∀ i, H (b i) = (E i : ℂ) • b i)
    (E₀ : ℝ) (hE₀ : ∀ i, E₀ ≤ E i)
    (ψ : V) (hψ : ψ ≠ 0) :
    E₀ ≤ (inner ℂ ψ (H ψ) : ℂ).re / (inner ℂ ψ ψ : ℂ).re := by
  have h : (inner ℂ ψ ψ : ℂ).re = ‖ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  rw [h]
  exact variational_bound_norm_sq b H E hE E₀ hE₀ ψ hψ

end QPhys

