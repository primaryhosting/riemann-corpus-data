/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Module

/-- **Variational principle (energy form).**
Let `H` be a symmetric (self-adjoint) operator on a finite-dimensional complex inner
product space (a Hamiltonian), with spectral eigenvalues `hH.eigenvalues hn` supplied by
the finite-dimensional spectral theorem, and let `E0` be a lower bound for all of them
(the ground-state energy). Then for every state `ψ`,
`E0 * ⟨ψ|ψ⟩ ≤ ⟨ψ|H|ψ⟩`.

The proof expands `ψ` in the orthonormal eigenbasis of `H`
(`LinearMap.IsSymmetric.eigenvectorBasis`, whose defining property is
`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`), giving
`⟨ψ|H|ψ⟩ = ∑ i, Eᵢ |cᵢ|²` and `⟨ψ|ψ⟩ = ∑ i, |cᵢ|²`. -/
theorem variational_bound_mul {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hn : finrank ℂ E = n)
    {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) (E0 : ℝ)
    (hE0 : ∀ i, E0 ≤ hH.eigenvalues hn i) (ψ : E) :
    E0 * RCLike.re ⟪ψ, ψ⟫_ℂ ≤ RCLike.re ⟪ψ, H ψ⟫_ℂ := by
  have hself : RCLike.re ⟪ψ, ψ⟫_ℂ = ‖ψ‖ ^ 2 := inner_self_eq_norm_sq ψ
  set b := hH.eigenvectorBasis hn with hb
  have hinner : RCLike.re ⟪ψ, H ψ⟫_ℂ
      = ∑ i, hH.eigenvalues hn i * ‖(b.repr ψ).ofLp i‖ ^ 2 := by
    rw [← b.repr.inner_map_map ψ (H ψ), PiLp.inner_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb, LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply, RCLike.inner_apply, ← hb,
      mul_assoc, Complex.mul_conj']
    norm_cast
    rw [RCLike.re_ofReal_mul]
    congr 1
  have hnorm : ‖ψ‖ ^ 2 = ∑ i, ‖(b.repr ψ).ofLp i‖ ^ 2 := by
    rw [← b.repr.norm_map ψ, EuclideanSpace.norm_sq_eq]
  rw [hinner, hself, hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hE0 i) (sq_nonneg _)

/-- **Variational bound.**
For a Hamiltonian `H` (a symmetric operator on a finite-dimensional complex inner product
space) whose eigenvalues are all at least the ground-state energy `E0`, and any nonzero
state `ψ`, the Rayleigh quotient satisfies `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E0`. -/
theorem variational_bound {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hn : finrank ℂ E = n)
    {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) (E0 : ℝ)
    (hE0 : ∀ i, E0 ≤ hH.eigenvalues hn i) (ψ : E) (hψ : ψ ≠ 0) :
    RCLike.re ⟪ψ, H ψ⟫_ℂ / RCLike.re ⟪ψ, ψ⟫_ℂ ≥ E0 := by
  have hpos : 0 < RCLike.re ⟪ψ, ψ⟫_ℂ := by
    rw [inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hψ) 2
  rw [ge_iff_le, le_div_iff₀ hpos]
  exact variational_bound_mul hn hH E0 hE0 ψ

/-- **The variational bound is sharp: the Rayleigh quotient of an eigenvector is its
eigenvalue.** -/
theorem rayleigh_eigenvectorBasis {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hn : finrank ℂ E = n)
    {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) (i : Fin n) :
    hH.eigenvectorBasis hn i ≠ 0 ∧
      RCLike.re ⟪hH.eigenvectorBasis hn i, H (hH.eigenvectorBasis hn i)⟫_ℂ /
          RCLike.re ⟪hH.eigenvectorBasis hn i, hH.eigenvectorBasis hn i⟫_ℂ
        = hH.eigenvalues hn i := by
  set b := hH.eigenvectorBasis hn with hb
  refine ⟨by simpa using b.orthonormal.ne_zero i, ?_⟩
  have hnorm : ‖b i‖ = 1 := b.orthonormal.1 i
  have hHb : H (b i) = ((hH.eigenvalues hn i : ℝ) : ℂ) • b i := by
    rw [hb]; exact hH.apply_eigenvectorBasis hn i
  rw [hHb, inner_smul_right, inner_self_eq_norm_sq, hnorm]
  simp

/-- **Ground-state variational principle.**
Taking `E0` to be the smallest eigenvalue of the Hamiltonian `H` (the ground-state
energy), every nonzero state satisfies `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E0`, and the bound is attained
by a ground state, so `E0` is exactly the minimum of the Rayleigh quotient. -/
theorem variational_bound_min {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hn : finrank ℂ E = n)
    {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    (∀ ψ : E, ψ ≠ 0 →
        RCLike.re ⟪ψ, H ψ⟫_ℂ / RCLike.re ⟪ψ, ψ⟫_ℂ
          ≥ Finset.univ.inf' hne (hH.eigenvalues hn)) ∧
      ∃ v : E, v ≠ 0 ∧ RCLike.re ⟪v, H v⟫_ℂ / RCLike.re ⟪v, v⟫_ℂ
          = Finset.univ.inf' hne (hH.eigenvalues hn) := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_inf' hne (hH.eigenvalues hn)
  refine ⟨fun ψ hψ => variational_bound hn hH _ (fun i => ?_) ψ hψ, ?_⟩
  · exact Finset.inf'_le _ (Finset.mem_univ i)
  · obtain ⟨hne0, hq⟩ := rayleigh_eigenvectorBasis hn hH i0
    exact ⟨hH.eigenvectorBasis hn i0, hne0, by rw [hq, hi0]⟩

end QPhys

