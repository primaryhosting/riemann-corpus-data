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

The Rayleigh–Ritz variational principle: if a Hamiltonian `H` is diagonal in an orthonormal
eigenbasis `b` with real eigenvalues `E i`, and `E0` is a lower bound for the spectrum (the
ground-state energy), then every nonzero state `psi` satisfies

`⟪psi, H psi⟫ / ⟪psi, psi⟫ ≥ E0`.

The key intermediate lemma is the spectral decomposition of the expectation value,
`QPhys.inner_eq_sum_eigen`.
-/

open scoped BigOperators InnerProductSpace

namespace QPhys

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Key intermediate lemma (spectral decomposition of the expectation value).**
If `H` acts diagonally on the orthonormal basis `b` with real eigenvalues `E i`, then the
expectation value `⟪psi, H psi⟫` is real and equals the weighted sum of the eigenvalues, the
weights being the squared moduli of the coefficients of `psi` in that basis. -/
theorem inner_eq_sum_eigen (b : OrthonormalBasis ι ℂ V) (H : V →L[ℂ] V) {E : ι → ℝ}
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (psi : V) :
    (⟪psi, H psi⟫_ℂ).re = ∑ i, E i * ‖⟪b i, psi⟫_ℂ‖ ^ 2 := by
  have hpsi : ∑ i, ⟪b i, psi⟫_ℂ • b i = psi := b.sum_repr' psi
  have hHpsi : H psi = ∑ i, (⟪b i, psi⟫_ℂ * (E i : ℂ)) • b i := by
    conv_lhs => rw [← hpsi]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hH i, smul_smul]
  have key : ⟪psi, H psi⟫_ℂ = ∑ i, ((E i : ℂ) * ((‖⟪b i, psi⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) := by
    rw [hHpsi, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : ⟪psi, b i⟫_ℂ = (starRingEnd ℂ) ⟪b i, psi⟫_ℂ := (inner_conj_symm _ _).symm
    have hz : (starRingEnd ℂ) ⟪b i, psi⟫_ℂ * ⟪b i, psi⟫_ℂ
        = ((‖⟪b i, psi⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.conj_mul]; norm_cast
    rw [inner_smul_right, hc, ← hz]
    ring
  rw [key, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Variational bound (Rayleigh–Ritz).**
Let `H` be a Hamiltonian on a complex inner product space, diagonal in the orthonormal
eigenbasis `b` with real eigenvalues `E i`, and let `E0` be a lower bound for the spectrum
(the ground-state energy). Then for every nonzero state `psi`,
`⟪psi, H psi⟫ / ⟪psi, psi⟫ ≥ E0`. -/
theorem variational_bound (b : OrthonormalBasis ι ℂ V) (H : V →L[ℂ] V) {E : ι → ℝ} {E0 : ℝ}
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (hE0 : ∀ i, E0 ≤ E i) {psi : V} (hpsi : psi ≠ 0) :
    E0 ≤ (⟪psi, H psi⟫_ℂ).re / (⟪psi, psi⟫_ℂ).re := by
  have hnorm : (⟪psi, psi⟫_ℂ).re = ‖psi‖ ^ 2 := by
    rw [← RCLike.re_eq_complex_re]; exact inner_self_eq_norm_sq psi
  have hpos : (0 : ℝ) < ‖psi‖ ^ 2 := by
    have : ‖psi‖ ≠ 0 := norm_ne_zero_iff.mpr hpsi
    positivity
  rw [hnorm, le_div_iff₀ hpos, inner_eq_sum_eigen b H hH psi,
    ← b.sum_sq_norm_inner_right psi, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hE0 i) (by positivity)

end QPhys

#print axioms QPhys.variational_bound

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

