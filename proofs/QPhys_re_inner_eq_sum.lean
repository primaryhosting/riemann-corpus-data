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

open scoped BigOperators InnerProductSpace

namespace QPhys

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Expansion of the inner product in an orthonormal basis. -/
private lemma inner_eq_sum_repr (b : OrthonormalBasis (Fin n) ℂ F) (x y : F) :
    inner ℂ x y = ∑ i, (starRingEnd ℂ) (b.repr x i) * b.repr y i := by
  rw [← b.repr.inner_map_map x y, PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

/-- Parseval: the squared norm is the sum of the squared moduli of the coordinates. -/
private lemma norm_sq_eq_sum_repr (b : OrthonormalBasis (Fin n) ℂ F) (x : F) :
    ‖x‖ ^ 2 = ∑ i, ‖b.repr x i‖ ^ 2 := by
  rw [← b.repr.norm_map x, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-- If `b` is an eigenbasis of `H` with eigenvalues `Ev`, then `H` acts diagonally on
coordinates. -/
private lemma repr_apply_of_eigenbasis (b : OrthonormalBasis (Fin n) ℂ F) (H : F →ₗ[ℂ] F)
    (Ev : Fin n → ℝ) (hH : ∀ i, H (b i) = (Ev i : ℂ) • b i) (ψ : F) (i : Fin n) :
    b.repr (H ψ) i = (Ev i : ℂ) * b.repr ψ i := by
  conv_lhs => rw [show ψ = ∑ j, b.repr ψ j • b j from (b.sum_repr ψ).symm]
  simp only [map_sum, map_smul, hH, OrthonormalBasis.repr_self]
  simp [Pi.single_apply, mul_comm]

/-- The expectation value `⟨ψ|H|ψ⟩` of an operator with orthonormal eigenbasis `b` and
(real) eigenvalues `Ev` is `∑ i, Ev i * |⟨b i|ψ⟩|²`. -/
lemma re_inner_eq_sum (b : OrthonormalBasis (Fin n) ℂ F) (H : F →ₗ[ℂ] F) (Ev : Fin n → ℝ)
    (hH : ∀ i, H (b i) = (Ev i : ℂ) • b i) (ψ : F) :
    (inner ℂ ψ (H ψ)).re = ∑ i, Ev i * ‖b.repr ψ i‖ ^ 2 := by
  rw [inner_eq_sum_repr b ψ (H ψ), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_apply_of_eigenbasis b H Ev hH ψ i]
  set z : ℂ := b.repr ψ i
  have h1 : (starRingEnd ℂ) z * ((Ev i : ℂ) * z) = (Ev i : ℂ) * ((starRingEnd ℂ) z * z) := by
    ring
  have h2 : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq z
  rw [h1, h2, ← Complex.ofReal_mul, Complex.ofReal_re]

/--
**Variational bound (Rayleigh–Ritz).**

Let `H` be an operator on a complex inner product space admitting an orthonormal
eigenbasis `b` with real eigenvalues `Ev` (the physical setting: `H` is a self-adjoint
Hamiltonian on a finite-dimensional state space), and let `E₀` be any lower bound for the
spectrum — in particular the ground-state energy `E₀ = min Ev`.

Then for every nonzero state `ψ`, the Rayleigh quotient satisfies

  `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E₀`,

where `⟨ψ|ψ⟩ = ‖ψ‖²`.
-/
theorem variational_bound (b : OrthonormalBasis (Fin n) ℂ F) (H : F →ₗ[ℂ] F)
    (Ev : Fin n → ℝ) (E0 : ℝ) (hH : ∀ i, H (b i) = (Ev i : ℂ) • b i)
    (hE0 : ∀ i, E0 ≤ Ev i) (ψ : F) (hψ : ψ ≠ 0) :
    E0 ≤ (inner ℂ ψ (H ψ)).re / ‖ψ‖ ^ 2 := by
  have hnorm : (0 : ℝ) < ‖ψ‖ ^ 2 := by positivity
  rw [le_div_iff₀ hnorm, re_inner_eq_sum b H Ev hH ψ, norm_sq_eq_sum_repr b ψ,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hE0 i) (by positivity)

/-- The bound of `QPhys.variational_bound` is attained at a ground-state eigenvector:
if `Ev i₀` is minimal, the Rayleigh quotient at `b i₀` equals `Ev i₀`. -/
theorem variational_bound_attained (b : OrthonormalBasis (Fin n) ℂ F) (H : F →ₗ[ℂ] F)
    (Ev : Fin n → ℝ) (hH : ∀ i, H (b i) = (Ev i : ℂ) • b i) (i0 : Fin n) :
    (inner ℂ (b i0) (H (b i0))).re / ‖b i0‖ ^ 2 = Ev i0 := by
  rw [re_inner_eq_sum b H Ev hH (b i0), b.norm_eq_one i0]
  simp [apply_ite (fun z : ℂ => ‖z‖ ^ 2)]

/-- Every family of real eigenvalues on an orthonormal basis is realized by an operator, so
the hypotheses of `QPhys.variational_bound` are satisfiable (non-vacuity). -/
theorem exists_eigenbasis_operator (b : OrthonormalBasis (Fin n) ℂ F) (Ev : Fin n → ℝ) :
    ∃ H : F →ₗ[ℂ] F, ∀ i, H (b i) = (Ev i : ℂ) • b i := by
  refine ⟨b.toBasis.constr ℂ (fun i => (Ev i : ℂ) • b i), fun i => ?_⟩
  rw [show b i = b.toBasis i from by rw [OrthonormalBasis.coe_toBasis],
    Module.Basis.constr_basis, OrthonormalBasis.coe_toBasis]

/-- A concrete instance: a two-level system with energies `+1` and `-1` has all Rayleigh
quotients bounded below by the ground-state energy `-1`, with equality at the ground state. -/
theorem variational_bound_two_level :
    ∃ H : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2),
      (∀ i, H (EuclideanSpace.basisFun (Fin 2) ℂ i)
          = ((![1, -1] i : ℝ) : ℂ) • EuclideanSpace.basisFun (Fin 2) ℂ i) ∧
      (∀ ψ : EuclideanSpace ℂ (Fin 2), ψ ≠ 0 → -1 ≤ (inner ℂ ψ (H ψ)).re / ‖ψ‖ ^ 2) ∧
      (inner ℂ (EuclideanSpace.basisFun (Fin 2) ℂ 1) (H (EuclideanSpace.basisFun (Fin 2) ℂ 1))).re
          / ‖EuclideanSpace.basisFun (Fin 2) ℂ 1‖ ^ 2 = -1 := by
  obtain ⟨H, hH⟩ := exists_eigenbasis_operator (EuclideanSpace.basisFun (Fin 2) ℂ) ![1, -1]
  refine ⟨H, hH, fun ψ hψ => ?_, ?_⟩
  · exact variational_bound _ H ![1, -1] (-1) hH (by intro i; fin_cases i <;> norm_num) ψ hψ
  · simpa using variational_bound_attained (EuclideanSpace.basisFun (Fin 2) ℂ) H ![1, -1] hH 1

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

